#include <stdlib.h>
#include <string.h>
#include <SWI-Prolog.h>
#include <CL/cl.h>
#include <CL/cl_ext.h>

/* Handles
 * =======
 * Each kind of OpenCL handle is a blob holding the handle.  Reference
 * counted handles are released when Prolog garbage collects their blob.
 */

#define HANDLE_BLOB(Kind, Release)                         \
  static int release_##Kind(atom_t a)                      \
  {                                                        \
    Kind *h = PL_blob_data(a, NULL, NULL);                 \
    if (h && *h)                                           \
      Release(*h);                                         \
    return TRUE;                                           \
  }                                                        \
  static PL_blob_t Kind##_blob = {                         \
    PL_BLOB_MAGIC, PL_BLOB_UNIQUE, #Kind, release_##Kind,  \
    NULL, NULL, NULL, NULL, NULL                           \
  };

#define NO_RELEASE(h) ((void)(h))

HANDLE_BLOB(cl_platform_id, NO_RELEASE)
HANDLE_BLOB(cl_device_id, NO_RELEASE)
HANDLE_BLOB(cl_context, clReleaseContext)
HANDLE_BLOB(cl_command_queue, clReleaseCommandQueue)
HANDLE_BLOB(cl_mem, clReleaseMemObject)
HANDLE_BLOB(cl_program, clReleaseProgram)
HANDLE_BLOB(cl_kernel, clReleaseKernel)
HANDLE_BLOB(cl_event, clReleaseEvent)

static int get_handle(term_t t, PL_blob_t *type, void *handle)
{
  void *data;
  size_t len;
  PL_blob_t *t_type;

  if (PL_get_blob(t, &data, &len, &t_type) && t_type == type)
  {
    memcpy(handle, data, sizeof(void *));
    return TRUE;
  }
  return PL_type_error(type->name, t);
}

static int unify_handle(term_t t, PL_blob_t *type, void *handle)
{
  return PL_unify_blob(t, &handle, sizeof(void *), type);
}

/* Errors
 * ======
 * A failing call raises error(opencl_error(Function, Code), _), where
 * Code is the name of the OpenCL error code.
 */

static const char *error_name(cl_int code)
{
  switch (code)
  {
    case CL_DEVICE_NOT_FOUND: return "CL_DEVICE_NOT_FOUND";
    case CL_DEVICE_NOT_AVAILABLE: return "CL_DEVICE_NOT_AVAILABLE";
    case CL_COMPILER_NOT_AVAILABLE: return "CL_COMPILER_NOT_AVAILABLE";
    case CL_MEM_OBJECT_ALLOCATION_FAILURE: return "CL_MEM_OBJECT_ALLOCATION_FAILURE";
    case CL_OUT_OF_RESOURCES: return "CL_OUT_OF_RESOURCES";
    case CL_OUT_OF_HOST_MEMORY: return "CL_OUT_OF_HOST_MEMORY";
    case CL_BUILD_PROGRAM_FAILURE: return "CL_BUILD_PROGRAM_FAILURE";
    case CL_INVALID_VALUE: return "CL_INVALID_VALUE";
    case CL_INVALID_DEVICE_TYPE: return "CL_INVALID_DEVICE_TYPE";
    case CL_INVALID_PLATFORM: return "CL_INVALID_PLATFORM";
    case CL_INVALID_DEVICE: return "CL_INVALID_DEVICE";
    case CL_INVALID_CONTEXT: return "CL_INVALID_CONTEXT";
    case CL_INVALID_QUEUE_PROPERTIES: return "CL_INVALID_QUEUE_PROPERTIES";
    case CL_INVALID_COMMAND_QUEUE: return "CL_INVALID_COMMAND_QUEUE";
    case CL_INVALID_MEM_OBJECT: return "CL_INVALID_MEM_OBJECT";
    case CL_INVALID_BUILD_OPTIONS: return "CL_INVALID_BUILD_OPTIONS";
    case CL_INVALID_PROGRAM: return "CL_INVALID_PROGRAM";
    case CL_INVALID_PROGRAM_EXECUTABLE: return "CL_INVALID_PROGRAM_EXECUTABLE";
    case CL_INVALID_KERNEL_NAME: return "CL_INVALID_KERNEL_NAME";
    case CL_INVALID_KERNEL: return "CL_INVALID_KERNEL";
    case CL_INVALID_ARG_INDEX: return "CL_INVALID_ARG_INDEX";
    case CL_INVALID_ARG_VALUE: return "CL_INVALID_ARG_VALUE";
    case CL_INVALID_ARG_SIZE: return "CL_INVALID_ARG_SIZE";
    case CL_INVALID_KERNEL_ARGS: return "CL_INVALID_KERNEL_ARGS";
    case CL_INVALID_WORK_DIMENSION: return "CL_INVALID_WORK_DIMENSION";
    case CL_INVALID_WORK_GROUP_SIZE: return "CL_INVALID_WORK_GROUP_SIZE";
    case CL_INVALID_GLOBAL_WORK_SIZE: return "CL_INVALID_GLOBAL_WORK_SIZE";
    case CL_INVALID_EVENT_WAIT_LIST: return "CL_INVALID_EVENT_WAIT_LIST";
    case CL_INVALID_EVENT: return "CL_INVALID_EVENT";
    case CL_INVALID_OPERATION: return "CL_INVALID_OPERATION";
    case CL_INVALID_BUFFER_SIZE: return "CL_INVALID_BUFFER_SIZE";
    case CL_EXEC_STATUS_ERROR_FOR_EVENTS_IN_WAIT_LIST:
      return "CL_EXEC_STATUS_ERROR_FOR_EVENTS_IN_WAIT_LIST";
    default: return "CL_UNKNOWN_ERROR";
  }
}

static int raise_error(cl_int code, const char *function, term_t context)
{
  term_t ex = PL_new_term_ref();

  return PL_unify_term(ex,
                       PL_FUNCTOR_CHARS, "error", 2,
                         PL_FUNCTOR_CHARS, "opencl_error", 2,
                           PL_CHARS, function,
                           PL_CHARS, error_name(code),
                         PL_TERM, context)
      && PL_raise_exception(ex);
}

static int check(cl_int code, const char *function)
{
  if (code == CL_SUCCESS)
    return TRUE;
  return raise_error(code, function, PL_new_term_ref());
}

/* Platforms and devices
 * =====================
 */

static foreign_t pl_cl_platforms(term_t list)
{
  cl_uint n;
  cl_int err = clGetPlatformIDs(0, NULL, &n);

  if (err == CL_PLATFORM_NOT_FOUND_KHR)
    return PL_unify_nil(list);
  if (!check(err, "clGetPlatformIDs"))
    return FALSE;

  cl_platform_id *ids = malloc(n * sizeof(cl_platform_id));
  if (!ids)
    return PL_resource_error("memory");
  err = clGetPlatformIDs(n, ids, NULL);

  term_t tail = PL_copy_term_ref(list);
  term_t head = PL_new_term_ref();
  int rc = check(err, "clGetPlatformIDs");
  for (cl_uint i = 0; rc && i < n; i++)
    rc = PL_unify_list(tail, head, tail)
      && unify_handle(head, &cl_platform_id_blob, ids[i]);
  free(ids);
  return rc && PL_unify_nil(tail);
}

static foreign_t pl_cl_devices(term_t platform_t, term_t list)
{
  cl_platform_id platform;
  cl_uint n;

  if (!get_handle(platform_t, &cl_platform_id_blob, &platform))
    return FALSE;
  cl_int err = clGetDeviceIDs(platform, CL_DEVICE_TYPE_ALL, 0, NULL, &n);
  if (err == CL_DEVICE_NOT_FOUND)
    return PL_unify_nil(list);
  if (!check(err, "clGetDeviceIDs"))
    return FALSE;

  cl_device_id *ids = malloc(n * sizeof(cl_device_id));
  if (!ids)
    return PL_resource_error("memory");
  err = clGetDeviceIDs(platform, CL_DEVICE_TYPE_ALL, n, ids, NULL);

  term_t tail = PL_copy_term_ref(list);
  term_t head = PL_new_term_ref();
  int rc = check(err, "clGetDeviceIDs");
  for (cl_uint i = 0; rc && i < n; i++)
    rc = PL_unify_list(tail, head, tail)
      && unify_handle(head, &cl_device_id_blob, ids[i]);
  free(ids);
  return rc && PL_unify_nil(tail);
}

typedef enum { INFO_STRING, INFO_ULONG, INFO_UINT, INFO_SIZE,
               INFO_DEVICE_TYPE, INFO_OUT_OF_ORDER } info_kind;

typedef struct
{
  const char *name;
  cl_uint param;
  info_kind kind;
} info_spec;

static const info_spec platform_infos[] = {
  { "name", CL_PLATFORM_NAME, INFO_STRING },
  { "vendor", CL_PLATFORM_VENDOR, INFO_STRING },
  { "version", CL_PLATFORM_VERSION, INFO_STRING },
  { NULL, 0, 0 }
};

static const info_spec device_infos[] = {
  { "name", CL_DEVICE_NAME, INFO_STRING },
  { "vendor", CL_DEVICE_VENDOR, INFO_STRING },
  { "version", CL_DEVICE_VERSION, INFO_STRING },
  { "driver_version", CL_DRIVER_VERSION, INFO_STRING },
  { "opencl_c_version", CL_DEVICE_OPENCL_C_VERSION, INFO_STRING },
  { "extensions", CL_DEVICE_EXTENSIONS, INFO_STRING },
  { "type", CL_DEVICE_TYPE, INFO_DEVICE_TYPE },
  { "global_mem_size", CL_DEVICE_GLOBAL_MEM_SIZE, INFO_ULONG },
  { "max_mem_alloc_size", CL_DEVICE_MAX_MEM_ALLOC_SIZE, INFO_ULONG },
  { "max_work_group_size", CL_DEVICE_MAX_WORK_GROUP_SIZE, INFO_SIZE },
  { "max_compute_units", CL_DEVICE_MAX_COMPUTE_UNITS, INFO_UINT },
  { "mem_base_addr_align", CL_DEVICE_MEM_BASE_ADDR_ALIGN, INFO_UINT },
  { "out_of_order", CL_DEVICE_QUEUE_ON_HOST_PROPERTIES, INFO_OUT_OF_ORDER },
  { NULL, 0, 0 }
};

typedef cl_int (*info_function)(void *, cl_uint, size_t, void *, size_t *);

static const info_spec *find_info(const info_spec *specs, term_t name_t)
{
  char *name;

  if (!PL_get_atom_chars(name_t, &name))
  {
    PL_type_error("atom", name_t);
    return NULL;
  }
  for (; specs->name; specs++)
    if (strcmp(specs->name, name) == 0)
      return specs;
  PL_domain_error("opencl_info", name_t);
  return NULL;
}

static const char *device_type_name(cl_device_type type)
{
  if (type & CL_DEVICE_TYPE_GPU) return "gpu";
  if (type & CL_DEVICE_TYPE_CPU) return "cpu";
  if (type & CL_DEVICE_TYPE_ACCELERATOR) return "accelerator";
  return "other";
}

static int unify_info(info_function get, const char *function, void *handle,
                      const info_spec *spec, term_t value)
{
  size_t size;
  cl_int err = get(handle, spec->param, 0, NULL, &size);

  if (!check(err, function))
    return FALSE;
  void *data = malloc(size);
  if (!data)
    return PL_resource_error("memory");
  err = get(handle, spec->param, size, data, NULL);

  int rc = check(err, function);
  if (rc)
  {
    switch (spec->kind)
    {
      case INFO_STRING:
        rc = PL_unify_chars(value, PL_STRING|REP_UTF8, (size_t)-1, data);
        break;
      case INFO_ULONG:
        rc = PL_unify_uint64(value, *(cl_ulong *)data);
        break;
      case INFO_UINT:
        rc = PL_unify_uint64(value, *(cl_uint *)data);
        break;
      case INFO_SIZE:
        rc = PL_unify_uint64(value, *(size_t *)data);
        break;
      case INFO_DEVICE_TYPE:
        rc = PL_unify_atom_chars(value,
                                 device_type_name(*(cl_device_type *)data));
        break;
      case INFO_OUT_OF_ORDER:
        rc = PL_unify_bool(value,
                           (*(cl_command_queue_properties *)data
                            & CL_QUEUE_OUT_OF_ORDER_EXEC_MODE_ENABLE) != 0);
        break;
    }
  }
  free(data);
  return rc;
}

static foreign_t pl_cl_platform_info(term_t platform_t, term_t name, term_t value)
{
  cl_platform_id platform;
  const info_spec *spec;

  return get_handle(platform_t, &cl_platform_id_blob, &platform)
    && (spec = find_info(platform_infos, name))
    && unify_info((info_function)clGetPlatformInfo, "clGetPlatformInfo",
                  platform, spec, value);
}

static foreign_t pl_cl_device_info(term_t device_t, term_t name, term_t value)
{
  cl_device_id device;
  const info_spec *spec;

  return get_handle(device_t, &cl_device_id_blob, &device)
    && (spec = find_info(device_infos, name))
    && unify_info((info_function)clGetDeviceInfo, "clGetDeviceInfo",
                  device, spec, value);
}

/* Contexts, queues and buffers
 * ============================
 */

static foreign_t pl_cl_context(term_t device_t, term_t context_t)
{
  cl_device_id device;
  cl_int err;

  if (!get_handle(device_t, &cl_device_id_blob, &device))
    return FALSE;
  cl_context context = clCreateContext(NULL, 1, &device, NULL, NULL, &err);
  return check(err, "clCreateContext")
    && unify_handle(context_t, &cl_context_blob, context);
}

static foreign_t pl_cl_queue(term_t context_t, term_t device_t,
                          term_t out_of_order_t, term_t queue_t)
{
  cl_context context;
  cl_device_id device;
  int out_of_order;
  cl_int err;

  if (!get_handle(context_t, &cl_context_blob, &context)
      || !get_handle(device_t, &cl_device_id_blob, &device)
      || !PL_get_bool_ex(out_of_order_t, &out_of_order))
    return FALSE;
  cl_queue_properties properties[] = {
    CL_QUEUE_PROPERTIES,
    out_of_order ? CL_QUEUE_OUT_OF_ORDER_EXEC_MODE_ENABLE : 0,
    0
  };
  cl_command_queue queue =
    clCreateCommandQueueWithProperties(context, device, properties, &err);
  return check(err, "clCreateCommandQueueWithProperties")
    && unify_handle(queue_t, &cl_command_queue_blob, queue);
}

static foreign_t pl_cl_buffer(term_t context_t, term_t bytes_t, term_t mem_t)
{
  cl_context context;
  size_t bytes;
  cl_int err;

  if (!get_handle(context_t, &cl_context_blob, &context)
      || !PL_get_size_ex(bytes_t, &bytes))
    return FALSE;
  cl_mem mem = clCreateBuffer(context, CL_MEM_READ_WRITE, bytes, NULL, &err);
  return check(err, "clCreateBuffer")
    && unify_handle(mem_t, &cl_mem_blob, mem);
}

/* Waits is a list of events: the command starts once they are complete. */
static int get_events(term_t list, cl_uint *n, cl_event **events)
{
  size_t len;

  if (PL_skip_list(list, 0, &len) != PL_LIST)
    return PL_type_error("list", list);
  *n = (cl_uint)len;
  *events = NULL;
  if (len == 0)
    return TRUE;
  *events = malloc(len * sizeof(cl_event));
  if (!*events)
    return PL_resource_error("memory");

  term_t tail = PL_copy_term_ref(list);
  term_t head = PL_new_term_ref();
  for (size_t i = 0; PL_get_list(tail, head, tail); i++)
  {
    if (!get_handle(head, &cl_event_blob, &(*events)[i]))
    {
      free(*events);
      return FALSE;
    }
  }
  return TRUE;
}

static foreign_t pl_cl_fill(term_t queue_t, term_t mem_t, term_t bytes_t,
                         term_t waits_t, term_t event_t)
{
  cl_command_queue queue;
  cl_mem mem;
  size_t bytes;
  cl_uint n_waits;
  cl_event *waits, event;
  cl_uchar zero = 0;

  if (!get_handle(queue_t, &cl_command_queue_blob, &queue)
      || !get_handle(mem_t, &cl_mem_blob, &mem)
      || !PL_get_size_ex(bytes_t, &bytes)
      || !get_events(waits_t, &n_waits, &waits))
    return FALSE;
  cl_int err = clEnqueueFillBuffer(queue, mem, &zero, sizeof(zero), 0, bytes,
                                   n_waits, waits, &event);
  free(waits);
  return check(err, "clEnqueueFillBuffer")
    && unify_handle(event_t, &cl_event_blob, event);
}

/* Blocking copies between a buffer and host memory, such as a C buffer
 * pointer from buffer.pl. */
static int copy(term_t queue_t, term_t mem_t, term_t offset_t,
                term_t pointer_t, term_t bytes_t, int write)
{
  cl_command_queue queue;
  cl_mem mem;
  size_t offset, bytes;
  void *pointer;

  if (!get_handle(queue_t, &cl_command_queue_blob, &queue)
      || !get_handle(mem_t, &cl_mem_blob, &mem)
      || !PL_get_size_ex(offset_t, &offset)
      || !PL_get_pointer_ex(pointer_t, &pointer)
      || !PL_get_size_ex(bytes_t, &bytes))
    return FALSE;
  if (write)
    return check(clEnqueueWriteBuffer(queue, mem, CL_TRUE, offset, bytes,
                                      pointer, 0, NULL, NULL),
                 "clEnqueueWriteBuffer");
  return check(clEnqueueReadBuffer(queue, mem, CL_TRUE, offset, bytes,
                                   pointer, 0, NULL, NULL),
               "clEnqueueReadBuffer");
}

static foreign_t pl_cl_write(term_t queue_t, term_t mem_t, term_t offset_t,
                          term_t pointer_t, term_t bytes_t)
{
  return copy(queue_t, mem_t, offset_t, pointer_t, bytes_t, TRUE);
}

static foreign_t pl_cl_read(term_t queue_t, term_t mem_t, term_t offset_t,
                         term_t pointer_t, term_t bytes_t)
{
  return copy(queue_t, mem_t, offset_t, pointer_t, bytes_t, FALSE);
}

/* Programs and kernels
 * ====================
 */

static int raise_build_error(cl_int code, cl_program program,
                             cl_device_id device)
{
  size_t size;
  term_t context = PL_new_term_ref();

  if (clGetProgramBuildInfo(program, device, CL_PROGRAM_BUILD_LOG, 0, NULL,
                            &size) == CL_SUCCESS)
  {
    char *log = malloc(size);
    if (log && clGetProgramBuildInfo(program, device, CL_PROGRAM_BUILD_LOG,
                                     size, log, NULL) == CL_SUCCESS)
    {
      if (!PL_unify_term(context,
                         PL_FUNCTOR_CHARS, "context", 2,
                           PL_VARIABLE,
                           PL_UTF8_STRING, log))
      {
        free(log);
        return FALSE;
      }
    }
    free(log);
  }
  return raise_error(code, "clBuildProgram", context);
}

static foreign_t pl_cl_program(term_t context_t, term_t device_t,
                            term_t source_t, term_t options_t,
                            term_t program_t)
{
  cl_context context;
  cl_device_id device;
  char *source, *options;
  size_t length;
  cl_int err;

  if (!get_handle(context_t, &cl_context_blob, &context)
      || !get_handle(device_t, &cl_device_id_blob, &device)
      || !PL_get_nchars(source_t, &length, &source,
                        CVT_ATOM|CVT_STRING|CVT_LIST|REP_UTF8|CVT_EXCEPTION
                        |BUF_STACK)
      || !PL_get_chars(options_t, &options,
                       CVT_ATOM|CVT_STRING|CVT_LIST|REP_UTF8|CVT_EXCEPTION
                       |BUF_STACK))
    return FALSE;
  const char *sources[] = { source };
  cl_program program =
    clCreateProgramWithSource(context, 1, sources, &length, &err);
  if (!check(err, "clCreateProgramWithSource"))
    return FALSE;
  err = clBuildProgram(program, 1, &device, options, NULL, NULL);
  if (err != CL_SUCCESS)
  {
    int rc = raise_build_error(err, program, device);
    clReleaseProgram(program);
    return rc;
  }
  return unify_handle(program_t, &cl_program_blob, program);
}

static foreign_t pl_cl_kernel(term_t program_t, term_t name_t, term_t kernel_t)
{
  cl_program program;
  char *name;
  cl_int err;

  if (!get_handle(program_t, &cl_program_blob, &program)
      || !PL_get_chars(name_t, &name, CVT_ATOM|CVT_STRING|CVT_EXCEPTION))
    return FALSE;
  cl_kernel kernel = clCreateKernel(program, name, &err);
  return check(err, "clCreateKernel")
    && unify_handle(kernel_t, &cl_kernel_blob, kernel);
}

/* An argument is mem(Buffer), int(Integer) for a cl_int or long(Integer)
 * for a cl_long. */
static int set_arg(cl_kernel kernel, cl_uint index, term_t arg)
{
  term_t value = PL_new_term_ref();
  atom_t name;
  size_t arity;

  if (!PL_get_name_arity(arg, &name, &arity) || arity != 1)
    return PL_domain_error("opencl_kernel_arg", arg);
  _PL_get_arg(1, arg, value);

  const char *kind = PL_atom_chars(name);
  cl_int err;
  if (strcmp(kind, "mem") == 0)
  {
    cl_mem mem;
    if (!get_handle(value, &cl_mem_blob, &mem))
      return FALSE;
    err = clSetKernelArg(kernel, index, sizeof(mem), &mem);
  } else if (strcmp(kind, "int") == 0)
  {
    int i;
    if (!PL_get_integer_ex(value, &i))
      return FALSE;
    cl_int v = i;
    err = clSetKernelArg(kernel, index, sizeof(v), &v);
  } else if (strcmp(kind, "long") == 0)
  {
    int64_t i;
    if (!PL_get_int64_ex(value, &i))
      return FALSE;
    cl_long v = i;
    err = clSetKernelArg(kernel, index, sizeof(v), &v);
  } else
    return PL_domain_error("opencl_kernel_arg", arg);
  return check(err, "clSetKernelArg");
}

/* Enqueue Kernel over a 1-dimensional range of Size work items.  The
 * arguments are captured when the kernel is enqueued. */
static foreign_t pl_cl_enqueue(term_t queue_t, term_t kernel_t, term_t args_t,
                            term_t size_t_, term_t waits_t, term_t event_t)
{
  cl_command_queue queue;
  cl_kernel kernel;
  size_t size;

  if (!get_handle(queue_t, &cl_command_queue_blob, &queue)
      || !get_handle(kernel_t, &cl_kernel_blob, &kernel)
      || !PL_get_size_ex(size_t_, &size))
    return FALSE;

  term_t tail = PL_copy_term_ref(args_t);
  term_t head = PL_new_term_ref();
  for (cl_uint i = 0; PL_get_list(tail, head, tail); i++)
    if (!set_arg(kernel, i, head))
      return FALSE;
  if (!PL_get_nil_ex(tail))
    return FALSE;

  cl_uint n_waits;
  cl_event *waits, event;
  if (!get_events(waits_t, &n_waits, &waits))
    return FALSE;
  cl_int err = clEnqueueNDRangeKernel(queue, kernel, 1, NULL, &size, NULL,
                                      n_waits, waits, &event);
  free(waits);
  return check(err, "clEnqueueNDRangeKernel")
    && unify_handle(event_t, &cl_event_blob, event);
}

static foreign_t pl_cl_wait(term_t events_t)
{
  cl_uint n;
  cl_event *events;

  if (!get_events(events_t, &n, &events))
    return FALSE;
  cl_int err = n > 0 ? clWaitForEvents(n, events) : CL_SUCCESS;
  free(events);
  return check(err, "clWaitForEvents");
}

static foreign_t pl_cl_finish(term_t queue_t)
{
  cl_command_queue queue;

  return get_handle(queue_t, &cl_command_queue_blob, &queue)
    && check(clFinish(queue), "clFinish");
}

install_t install_opencl(void)
{
  PL_register_foreign("cl_platforms", 1, pl_cl_platforms, 0);
  PL_register_foreign("cl_devices", 2, pl_cl_devices, 0);
  PL_register_foreign("cl_platform_info", 3, pl_cl_platform_info, 0);
  PL_register_foreign("cl_device_info", 3, pl_cl_device_info, 0);
  PL_register_foreign("cl_context", 2, pl_cl_context, 0);
  PL_register_foreign("cl_queue", 4, pl_cl_queue, 0);
  PL_register_foreign("cl_buffer", 3, pl_cl_buffer, 0);
  PL_register_foreign("cl_fill", 5, pl_cl_fill, 0);
  PL_register_foreign("cl_write", 5, pl_cl_write, 0);
  PL_register_foreign("cl_read", 5, pl_cl_read, 0);
  PL_register_foreign("cl_program", 5, pl_cl_program, 0);
  PL_register_foreign("cl_kernel", 3, pl_cl_kernel, 0);
  PL_register_foreign("cl_enqueue", 6, pl_cl_enqueue, 0);
  PL_register_foreign("cl_wait", 1, pl_cl_wait, 0);
  PL_register_foreign("cl_finish", 1, pl_cl_finish, 0);
}
