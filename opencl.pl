:- module(opencl, [
   opencl_device/2,
   cl_platforms/1,
   cl_devices/2,
   cl_platform_info/3,
   cl_device_info/3,
   cl_context/2,
   cl_queue/4,
   cl_buffer/3,
   cl_fill/5,
   cl_write/5,
   cl_read/5,
   cl_program/5,
   cl_kernel/3,
   cl_enqueue/6,
   cl_wait/1,
   cl_finish/1
]).

/** <module> OpenCL host API

A thin binding of the OpenCL host API, from opencl.c:
  * cl_platforms(-Platforms), cl_devices(+Platform, -Devices)
  * cl_platform_info(+Platform, +Name, -Value) for name, vendor and version
  * cl_device_info(+Device, +Name, -Value) for name, vendor, version,
    driver_version, opencl_c_version, extensions, type (cpu, gpu,
    accelerator or other), global_mem_size, max_mem_alloc_size,
    max_work_group_size, max_compute_units, mem_base_addr_align (bits) and
    out_of_order (whether a queue can execute out of order)
  * cl_context(+Device, -Context)
  * cl_queue(+Context, +Device, +OutOfOrder, -Queue)
  * cl_buffer(+Context, +Bytes, -Buffer)
  * cl_fill(+Queue, +Buffer, +Bytes, +Waits, -Event): zero Buffer
  * cl_write(+Queue, +Buffer, +Offset, +Pointer, +Bytes) and
    cl_read(+Queue, +Buffer, +Offset, +Pointer, +Bytes): blocking copies
    between Buffer and host memory, such as a C buffer of buffer.pl
  * cl_program(+Context, +Device, +Source, +Options, -Program)
  * cl_kernel(+Program, +Name, -Kernel)
  * cl_enqueue(+Queue, +Kernel, +Args, +Size, +Waits, -Event): run Kernel
    over Size work items, with Args a list of mem(Buffer), int(I) and
    long(I)
  * cl_wait(+Events), cl_finish(+Queue)

Waits is a list of events a command waits for.
Handles are released when they are garbage collected.
A failing call raises error(opencl_error(Function, Code), Context), where
Code is the name of the OpenCL error code.
*/

:- use_module(buffer, []).
:- use_foreign_library(foreign(opencl)).

% opencl_device(?Name, ?Device)
% Device is the OpenCL device named Name.
% A device is named after its platform: pocl, nvidia, intel, amd...
% Further devices of a platform are named Name_1, Name_2...
opencl_device(Name, Device) :-
   findall(Base-Device0, platform_device(Base, Device0), Pairs),
   name_devices(Pairs, [], Named),
   member(Name-Device, Named).

platform_device(Base, Device) :-
   cl_platforms(Platforms),
   member(Platform, Platforms),
   cl_platform_info(Platform, name, PlatformName),
   platform_base_name(PlatformName, Base),
   cl_devices(Platform, Devices),
   member(Device, Devices).

platform_base_name(Name, Base), sub_string(Name, _, _, _, "Portable Computing Language") =>
   Base = pocl.
platform_base_name(Name, Base), sub_string(Name, _, _, _, "NVIDIA") =>
   Base = nvidia.
platform_base_name(Name, Base), sub_string(Name, _, _, _, "Intel") =>
   Base = intel.
platform_base_name(Name, Base), sub_string(Name, _, _, _, "AMD") =>
   Base = amd.
platform_base_name(Name, Base), sub_string(Name, _, _, _, "rusticl") =>
   Base = rusticl.
platform_base_name(Name, Base) =>
   split_string(Name, " ", " ", [First | _]),
   string_lower(First, Lower),
   atom_string(Base, Lower).

% The first device of a base name takes it, the next ones a suffix.
name_devices([], _, Named) =>
   Named = [].
name_devices([Base-Device | Pairs], Seen, Named) =>
   aggregate_all(count, member(Base, Seen), N),
   device_name(Base, N, Name),
   Named = [Name-Device | Named1],
   name_devices(Pairs, [Base | Seen], Named1).

device_name(Base, 0, Name) =>
   Name = Base.
device_name(Base, N, Name) =>
   atomic_list_concat([Base, N], '_', Name).

:- begin_tests(opencl).

:- use_module(buffer).

device_queue(Device, Context, Queue) :-
   cl_context(Device, Context),
   cl_queue(Context, Device, false, Queue).

test('devices have distinct names') :-
   findall(Name, opencl_device(Name, _), Names),
   Names \== [],
   sort(Names, Sorted),
   length(Names, N),
   length(Sorted, N).

test('buffer round trip', [forall(opencl_device(_, Device))]) :-
   device_queue(Device, Context, Queue),
   Values = [1.5, -2.0, 3.25],
   Data =.. [data | Values],
   buffer_from_data(In, float64, 3, Data),
   buffer_offset(In, float64, 3, 0, InPointer),
   cl_buffer(Context, 24, Mem),
   cl_write(Queue, Mem, 0, InPointer, 24),
   buffer_alloc(Out, float64, 3, true),
   buffer_offset(Out, float64, 3, 0, OutPointer),
   cl_read(Queue, Mem, 0, OutPointer, 24),
   buffer_to_data(Out, float64, 3, Data1),
   Data1 == Data.

add_one("__kernel void add_one(__global int *a) {
   size_t i = get_global_id(0);
   a[i] += 1;
}").

test('kernel adds one', [forall(opencl_device(_, Device))]) :-
   device_queue(Device, Context, Queue),
   add_one(Source),
   cl_program(Context, Device, Source, "", Program),
   cl_kernel(Program, add_one, Kernel),
   buffer_from_data(Host, int32, 4, data(1, 2, 3, 4)),
   buffer_offset(Host, int32, 4, 0, Pointer),
   cl_buffer(Context, 16, Mem),
   cl_write(Queue, Mem, 0, Pointer, 16),
   cl_enqueue(Queue, Kernel, [mem(Mem)], 4, [], Event),
   cl_wait([Event]),
   cl_read(Queue, Mem, 0, Pointer, 16),
   buffer_to_data(Host, int32, 4, Data),
   Data == data(2, 3, 4, 5).

scale_add("__kernel void scale(__global int *a, __global int *b, int k) {
   size_t i = get_global_id(0);
   b[i] = a[i] * k;
}
__kernel void add(__global int *b, __global int *c, long k) {
   size_t i = get_global_id(0);
   c[i] = b[i] + k;
}").

test('events order kernels on an out-of-order queue',
     [forall((opencl_device(_, Device), cl_device_info(Device, out_of_order, true)))]) :-
   cl_context(Device, Context),
   cl_queue(Context, Device, true, Queue),
   scale_add(Source),
   cl_program(Context, Device, Source, "", Program),
   cl_kernel(Program, scale, Scale),
   cl_kernel(Program, add, Add),
   N = 1024,
   Bytes is 4 * N,
   numlist(1, N, Values),
   Data =.. [data | Values],
   buffer_from_data(Host, int32, N, Data),
   buffer_offset(Host, int32, N, 0, Pointer),
   cl_buffer(Context, Bytes, A),
   cl_buffer(Context, Bytes, B),
   cl_buffer(Context, Bytes, C),
   cl_write(Queue, A, 0, Pointer, Bytes),
   cl_enqueue(Queue, Scale, [mem(A), mem(B), int(2)], N, [], Scaled),
   cl_enqueue(Queue, Add, [mem(B), mem(C), long(1)], N, [Scaled], Added),
   cl_wait([Added]),
   cl_read(Queue, C, 0, Pointer, Bytes),
   buffer_to_data(Host, int32, N, Result),
   Result =.. [data | Results],
   maplist([X, Y]>>(Y =:= 2*X + 1), Values, Results).

test('fill zeroes a buffer', [forall(opencl_device(_, Device))]) :-
   device_queue(Device, Context, Queue),
   buffer_from_data(Host, int32, 3, data(7, 8, 9)),
   buffer_offset(Host, int32, 3, 0, Pointer),
   cl_buffer(Context, 12, Mem),
   cl_write(Queue, Mem, 0, Pointer, 12),
   cl_fill(Queue, Mem, 12, [], Filled),
   cl_wait([Filled]),
   cl_read(Queue, Mem, 0, Pointer, 12),
   buffer_to_data(Host, int32, 3, Data),
   Data == data(0, 0, 0).

test('a build error carries the build log', [forall(opencl_device(_, Device))]) :-
   cl_context(Device, Context),
   catch(cl_program(Context, Device, "__kernel void f( { }", "", _),
         error(opencl_error(clBuildProgram, Code), context(_, Log)),
         true),
   Code == 'CL_BUILD_PROGRAM_FAILURE',
   string(Log),
   Log \== "".

:- end_tests(opencl).
