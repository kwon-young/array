:- module(opencl_tests, []).

:- use_module(library(array/opencl)).
:- use_module(library(array/buffer)).

:- begin_tests(opencl).

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

test('a sub-buffer shares the memory of its buffer', [forall(opencl_device(_, Device))]) :-
   device_queue(Device, Context, Queue),
   cl_device_info(Device, mem_base_addr_align, Bits), Align is Bits // 8,
   Bytes is 2*Align,
   cl_buffer(Context, Bytes, Mem),
   cl_sub_buffer(Mem, Align, 12, Sub),
   buffer_from_data(Host, int32, 3, data(7, 8, 9)),
   buffer_offset(Host, int32, 3, 0, Pointer),
   cl_write(Queue, Sub, 0, Pointer, 12),
   buffer_alloc(Out, int32, 3, true),
   buffer_offset(Out, int32, 3, 0, OutPointer),
   cl_read(Queue, Mem, Align, OutPointer, 12),
   buffer_to_data(Out, int32, 3, Data),
   Data == data(7, 8, 9),
   catch(cl_sub_buffer(Mem, 1, 12, _), error(opencl_error(clCreateSubBuffer, _), _), true),
   % arenas and their slices dropped in whatever order survive the collector
   forall(between(1, 50, _), ( cl_buffer(Context, Bytes, Arena), cl_sub_buffer(Arena, 0, Align, _),
                               cl_sub_buffer(Arena, Align, Align, _) )),
   garbage_collect_atoms.

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
