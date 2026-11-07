:- module(opencl, [
   opencl_device/2,
   cl_platforms/1,
   cl_devices/2,
   cl_platform_info/3,
   cl_device_info/3,
   cl_context/2,
   cl_queue/4,
   cl_buffer/3,
   cl_sub_buffer/4,
   cl_fill/5,
   cl_write/5,
   cl_read/5,
   cl_program/5,
   cl_kernel/3,
   cl_program_log/3,
   cl_program_binary/2,
   cl_enqueue/6,
   cl_enqueue/7,
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
    max_work_group_size, max_compute_units, mem_base_addr_align (bits),
    out_of_order (whether a queue can execute out of order), local_mem_size,
    local_mem_type (local, or global when emulated), global_mem_cache_size,
    global_mem_cacheline_size, preferred_vector_width_float,
    native_vector_width_float, max_clock_frequency (MHz), and warp_size or
    wavefront_width, which fail on devices without the NVIDIA or AMD extension
  * cl_context(+Device, -Context)
  * cl_queue(+Context, +Device, +OutOfOrder, -Queue)
  * cl_buffer(+Context, +Bytes, -Buffer)
  * cl_sub_buffer(+Buffer, +Offset, +Bytes, -Sub): Bytes of Buffer from Offset,
    a multiple of the device's mem_base_addr_align in bytes, as a buffer of its
    own, sharing the memory
  * cl_fill(+Queue, +Buffer, +Bytes, +Waits, -Event): zero Buffer
  * cl_write(+Queue, +Buffer, +Offset, +Pointer, +Bytes) and
    cl_read(+Queue, +Buffer, +Offset, +Pointer, +Bytes): blocking copies
    between Buffer and host memory, such as a C buffer of buffer.pl
  * cl_program(+Context, +Device, +Source, +Options, -Program)
  * cl_kernel(+Program, +Name, -Kernel)
  * cl_program_log(+Program, +Device, -Log): the build log, with -cl-nv-verbose
    the register use on NVIDIA
  * cl_program_binary(+Program, -Binary): the first binary, PTX on NVIDIA
  * cl_enqueue(+Queue, +Kernel, +Args, +Size, +Waits, -Event): run Kernel
    over Size work items, with Args a list of mem(Buffer), int(I) and
    long(I)
  * cl_enqueue(+Queue, +Kernel, +Args, +Global, +Local, +Waits, -Event): the
    same, in work-groups of Local work items, chosen by the device when 0
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
opencl_device(Name, Device), atom(Name) =>
   named_devices(Named),
   memberchk(Name-Device0, Named),
   Device = Device0.
opencl_device(Name, Device) =>
   named_devices(Named),
   member(Name-Device, Named).

% The devices are enumerated once, by one thread: a runtime initialises its devices on the
% first clGetDeviceIDs, and reports none to a thread asking while it does (pocl), so threads
% enumerating a cold process at once would see different tables.
:- dynamic device_table/1.

named_devices(Named) :-
   with_mutex(opencl_devices, named_devices_(Named)).

named_devices_(Named), device_table(Table) =>
   Named = Table.
named_devices_(Named) =>
   findall(Base-Device, platform_device(Base, Device), Pairs),
   name_devices(Pairs, [], Named),
   assertz(device_table(Named)).

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
