:- module(runtime_opencl, []).

/** <module> OpenCL device

An array on the device opencl(Name) lives in a buffer of the OpenCL device
named Name (see opencl:opencl_device/2), such as opencl(pocl) or
opencl(nvidia).

It exchanges data with the C device only: a transfer is a byte copy between
an OpenCL buffer and a C buffer of the same format, so it is exact.
Prolog data goes through the C device.
*/

:- use_module(array, []).
:- use_module(buffer).
:- use_module(c99).
:- use_module(kernel_c).
:- use_module(ir_lower, [lower_kernel/5]).
:- use_module(ir_optimize, [optimize_kernel/3]).
:- use_module(ir_c, [ir_c/3]).
:- use_module(opencl).
:- use_module(swipl_ld, [clang_format/2]).

% Devices
% =======

% device_state(Name, Device, Context, Queue): a device is set up on its first
% use, and kept for the session.
:- dynamic device_state/4.

device(Name, Device, Context, Queue), device_state(Name, Device0, Context0, Queue0) =>
   Device = Device0,
   Context = Context0,
   Queue = Queue0.
device(Name, Device, Context, Queue), opencl_device(Name, Device0) =>
   cl_context(Device0, Context0),
   cl_queue(Context0, Device0, false, Queue0),
   assertz(device_state(Name, Device0, Context0, Queue0)),
   Device = Device0,
   Context = Context0,
   Queue = Queue0.
device(Name, _, _, _) =>
   existence_error(opencl_device, Name).

% A device stores the formats of the C device, except float16 and float64
% without their extension.
supported_format(Device, float16) =>
   extension(Device, "cl_khr_fp16").
supported_format(Device, float64) =>
   extension(Device, "cl_khr_fp64").
supported_format(_, _) =>
   true.

extension(Device, Extension) :-
   cl_device_info(Device, extensions, Extensions),
   split_string(Extensions, " ", " ", Names),
   memberchk(Extension, Names).

% Formats
% =======

ir_optimize:layers(opencl(_), Layers) :-
   ir_optimize:layers(c, Layers).

array:default_format(opencl(_), M, Format) :-
   array:default_format(c, M, Format).
array:float_formats(opencl(Name), Formats) :-
   opencl_device(Name, Device),
   array:float_formats(c, CFormats),
   include(supported_format(Device), CFormats, Formats).
array:M.dtype_size(opencl(_)) := Size :-
   buffer_type_size(M.dtype(), Size).
array:expression_op(opencl(_), Op) :-
   array:expression_op(c, Op).
array:compute_format(opencl(_), Formats, Format) :-
   array:compute_format(c, Formats, Format).

% Kernels
% =======

array:M.compile(opencl(_), true) := Dict :-
   Dict = M.put(kernel, true).
array:M.compile(opencl(_), view(_)) := Dict :-
   Dict = M.put(kernel, true).
array:M.compile(opencl(_), constant(_)) := Dict :-
   Dict = M.put(kernel, true).
% OpenCL C has no random numbers.
array:_M.compile(opencl(Name), rand) := _Dict :-
   throw(error(unsupported_op(opencl(Name), rand), _)).
array:_M.compile(opencl(Name), solve(_, _)) := _Dict :-
   throw(error(unsupported_op(opencl(Name), solve), _)).
array:M.compile(opencl(Name), Op) := Dict :-
   compile_kernel(Name, M, Op, Dict).

% compile_kernel(+Name, +M, +Op, -Dict)
% Dict is M with a kernel computing Op into M: the kernel IR of Op, printed
% in OpenCL C. The kernel runs one work item per element of M, which
% unravels its global id into the element's index.
compile_kernel(Name, M, Op, Dict) :-
   lower_kernel(opencl(Name), M, Op, IR0, Arrays),
   ir_kernel(Name, IR0, Kernel, Size),
   maplist(kernel_arg, Arrays, KernelArgs),
   Dict = M.put(kernel, runtime_opencl:launch(Name, Kernel, KernelArgs, Size)).

% ir_kernel(+Name, +IR0, -Kernel, -Size)
% Kernel runs the IR clause IR0 on device Name, one work item per index of
% the domain of its outer forall, of Size indices: an iterate inside runs in
% order in its work item.
ir_kernel(Name, IR0, Kernel, Size) :-
   optimize_kernel(opencl(Name), IR0, IR),
   ir_c(opencl, IR, c_kernel(Buffers, Shape, TypeIndex, Body)),
   maplist(index_name, TypeIndex, Index),
   Exprs = view{}.from_shape(Shape).reverse_index_expr(g),
   maplist(index_declaration, Index, Exprs, Declarations),
   maplist(param, Buffers, Params),
   opt_level(Level),
   Code = kernel(Level, Params, Declarations, Body),
   % A kernel is named after its code, so a kernel already built is reused.
   variant_sha1(Code, Hash),
   atom_concat(kernel_, Hash, KernelName),
   load_kernel(Name, KernelName, Level, Code, Kernel),
   foldl([D, S0, S1]>>(S1 is S0*D), Shape, 1, Size).

% Runs the IR clause Kernel on Datas, its outputs unbound data(...) terms,
% through device buffers of the formats of its head.
array:run_ir(opencl(Name), Kernel, Datas) :-
   ir_kernel(Name, Kernel, ClKernel, Size),
   device(Name, Device, Context, Queue),
   runtime_c:head_formats(Kernel, Formats),
   maplist(check_format(Name, Device), Formats),
   maplist(runtime_c:data_buffer, Datas, Formats, Hosts),
   maplist(device_buffer(Context, Queue), Datas, Formats, Hosts, Mems),
   maplist([Mem, mem(Mem)]>>true, Mems, Args),
   launch(Name, ClKernel, Args, Size),
   maplist(host_buffer(Queue), Datas, Formats, Hosts, Mems),
   maplist(runtime_c:buffer_data, Datas, Formats, Hosts).

device_buffer(Context, Queue, Data, Format, Host, Mem) :-
   functor(Data, _, N),
   buffer_type_size(Format, TypeSize),
   Bytes is N*TypeSize,
   buffer(Context, Bytes, Mem),
   buffer_offset(Host, Format, N, 0, Pointer),
   copy(cl_write, Queue, Mem, 0, Pointer, Bytes).

host_buffer(_, Data, _, _, _), ground(Data) =>
   true.
host_buffer(Queue, Data, Format, Host, Mem) =>
   functor(Data, _, N),
   buffer_type_size(Format, TypeSize),
   Bytes is N*TypeSize,
   buffer_offset(Host, Format, N, 0, Pointer),
   copy(cl_read, Queue, Mem, 0, Pointer, Bytes).

index_name(_:I, I).

index_declaration(I, Expr, long:I = Expr).

kernel_arg(A, mem(Data)) :-
   get_dict(data, A, Data).

% a0 is the output: it never overlaps an input, which lives in the buffer pool
% until its reader has run.
param(Format-Name, Type:Name) :-
   type_name(opencl, Format, Element),
   param_qualifiers(Name, Qualifiers),
   atomic_list_concat(['__global ', Qualifiers, Element, ' *restrict'], Type).

param_qualifiers(a0, Qualifiers) =>
   Qualifiers = ''.
param_qualifiers(_, Qualifiers) =>
   Qualifiers = 'const '.

kernel_source(Name, KernelName, kernel(_Level, Params, Declarations, Body), Source) :-
   Head =.. [KernelName | Params],
   append([long:g = get_global_id(0) | Declarations], [Body], List),
   statements(List, Statements),
   AST = ('__kernel void':Head { Statements }),
   name_variables(AST),
   once(phrase(translation_unit(AST), Tokens)),
   once(phrase(tokens(Tokens), Codes)),
   clang_format(Codes, Formatted),
   device(Name, Device, _, _),
   pragmas(Device, Pragmas),
   string_codes(Kernel, Formatted),
   string_concat(Pragmas, Kernel, Source).

pragmas(Device, Pragmas), extension(Device, "cl_khr_fp64") =>
   Pragmas = "#pragma OPENCL EXTENSION cl_khr_fp64 : enable\n".
pragmas(_, Pragmas) =>
   Pragmas = "".

% device_kernel(Name, KernelName, Kernel): the kernels built on a device.
:- dynamic device_kernel/3.

load_kernel(Name, KernelName, _, _, Kernel), device_kernel(Name, KernelName, Kernel0) =>
   Kernel = Kernel0.
load_kernel(Name, KernelName, Level, Code, Kernel) =>
   device(Name, Device, Context, _),
   kernel_source(Name, KernelName, Code, Source),
   debug(array(kernel), "~s", [Source]),
   build_options(Level, Options),
   cl_program(Context, Device, Source, Options, Program),
   cl_kernel(Program, KernelName, Kernel),
   assertz(device_kernel(Name, KernelName, Kernel)).

% OpenCL compilers optimize unless told not to.
build_options(0, Options) =>
   Options = "-cl-opt-disable".
build_options(_, Options) =>
   Options = "".

% The device runs the kernels of a schedule in order: its queue is in order.
launch(_, _, _, 0) =>
   true.
launch(Name, Kernel, Args, Size) =>
   device(Name, _, _, Queue),
   cl_enqueue(Queue, Kernel, Args, Size, [], _).

% Buffers
% =======

array:allocate(opencl(Name), M) :-
   device(Name, _, Context, Queue),
   Bytes is M.datasize * M.dtype_size(),
   buffer(Context, Bytes, M.data),
   cl_fill(Queue, M.data, Bytes, [], Filled),
   cl_wait([Filled]).

% Transfers
% =========

array:M.to(c, opencl(Name)) := Dict :-
   M1 = M.contiguous().realize(),
   device(Name, Device, Context, Queue),
   Format = M1.dtype(),
   check_format(Name, Device, Format),
   bytes(M1, Offset, Bytes),
   buffer_offset(M1.data, Format, M1.datasize, 0, Pointer0),
   Pointer is Pointer0 + Offset,
   buffer(Context, Bytes, Mem),
   copy(cl_write, Queue, Mem, 0, Pointer, Bytes),
   Dict = M.empty(M1.shape(), [device(opencl(Name)), data(Mem), format(Format),
                               precision(M1.precision)]).

array:M.to(opencl(Name), c) := Dict :-
   M1 = M.contiguous().realize(),
   device(Name, _, _, Queue),
   Format = M1.dtype(),
   Size = M1.size(),
   bytes(M1, Offset, Bytes),
   buffer_alloc(Buffer, Format, Size, false),
   buffer_offset(Buffer, Format, Size, 0, Pointer),
   copy(cl_read, Queue, M1.data, Offset, Pointer, Bytes),
   Dict = M.empty(M1.shape(), [device(c), data(Buffer), format(Format),
                               precision(M1.precision)]).

% Prolog and OpenCL exchange data through the C device.
array:M.to(prolog, opencl(Name)) := Dict :-
   Dict = M.to(c).to(opencl(Name)).
array:M.to(opencl(_Name), prolog) := Dict :-
   Dict = M.to(c).to(prolog).

check_format(_, Device, Format), supported_format(Device, Format) =>
   true.
check_format(Name, _, Format) =>
   throw(error(unsupported_format(opencl(Name), Format), _)).

% The elements of a contiguous array are the Bytes from Offset in its buffer.
bytes(M, Offset, Bytes) :-
   Size = M.dtype_size(),
   Offset is M.data_offset() * Size,
   Bytes is M.size() * Size.

% OpenCL has no empty buffer.
buffer(Context, Bytes, Mem) :-
   Size is max(1, Bytes),
   cl_buffer(Context, Size, Mem).

% OpenCL has no empty copy.
copy(_, _, _, _, _, 0) =>
   true.
copy(Copy, Queue, Mem, Offset, Pointer, Bytes) =>
   call(Copy, Queue, Mem, Offset, Pointer, Bytes).

:- multifile prolog:error_message//1.

prolog:error_message(unsupported_format(Device, Format)) -->
   [ 'The device ~w has no ~w format'-[Device, Format] ].
prolog:error_message(unsupported_op(Device, Op)) -->
   [ 'The device ~w can\'t compute ~w'-[Device, Op] ].

:- begin_tests(opencl_device).

:- use_module(array).

% A C array of Values in Format.
c_array(Values, Kind, Format, A) :-
   length(Values, N),
   Data =.. [data | Values],
   buffer_from_data(Buffer, Format, N, Data),
   A = array{}.empty([N], [device(c), dtype(Kind), data(Buffer),
                           format(Format)]).

c_values(int8, integer, [-128, 0, 127]).
c_values(uint8, integer, [0, 1, 255]).
c_values(int16, integer, [-32768, 7, 32767]).
c_values(uint16, integer, [0, 7, 65535]).
c_values(int32, integer, [-2147483648, 7, 2147483647]).
c_values(uint32, integer, [0, 7, 4294967295]).
c_values(int64, integer, [-9223372036854775808, 7, 9223372036854775807]).
c_values(uint64, integer, [0, 7, 18446744073709551615]).
c_values(bool, boolean, [0, 1, 1]).
c_values(float32, float, [1.5, -0.25, 1024.0]).
c_values(float64, float, [1.5, -0.1, 1.0e300]).

device_format(Name, Format, Kind, Values) :-
   opencl_device(Name, Device),
   c_values(Format, Kind, Values),
   supported_format(Device, Format).

test('c round trip keeps the format and the values',
     [forall(device_format(Name, Format, Kind, Values))]) :-
   c_array(Values, Kind, Format, A),
   B = A.to(opencl(Name)),
   B.dtype() == Format,
   C = B.to(c),
   C.dtype() == Format,
   C.tolist() == Values.

test('prolog round trip', [forall(opencl_device(Name, _))]) :-
   forall(member(L, [[1, -2, 300], [[1.5, -2.25], [0.5, 4.0]], [0, 1, 1]]),
          (  A = array{}.fromlist(L, [device(opencl(Name))]),
             A.device == opencl(Name),
             A.tolist() == L
          )).

test('a slice is transferred alone',
     [forall(opencl_device(Name, _)), timeout(30)]) :-
   A = array{}.fromlist([1.0, 2.0, 3.0], [device(c)]),
   Suffix = A.shrink([1-3]),
   B = Suffix.to(opencl(Name)),
   B.tolist() == [2.0, 3.0],
   C = array{}.fromlist([1.0, 2.0, 3.0], [device(opencl(Name))]),
   Prefix = C.shrink([0-2]),
   Prefix.to(c).tolist() == [1.0, 2.0].

test('allocation is zeroed', [forall(opencl_device(Name, _))]) :-
   A = array{}.empty([3], [device(opencl(Name)), dtype(integer),
                           format(int32)]),
   array:allocate(A.device, A),
   A.tolist() == [0, 0, 0].

test('a format without its extension fails loudly',
     [forall((opencl_device(Name, Device), \+ supported_format(Device, float16)))]) :-
   c_array([1.5], float, float16, A),
   catch(_ = A.to(opencl(Name)), error(E, _), true),
   E == unsupported_format(opencl(Name), float16).

test('an unknown device fails loudly',
     [throws(error(existence_error(opencl_device, nowhere), _))]) :-
   _ = array{}.fromlist([1], [device(opencl(nowhere))]).

:- end_tests(opencl_device).

:- begin_tests(opencl_kernel).

:- use_module(array).

% case(Name, Inputs): Inputs are the lists of the arrays graph/3 computes on.
case(chain, [[1.0, 2.0, 3.0]]).
case(compare_wide, [[70000, 3]]).
case(round, [[1.0, 2.0, -1.4]]).
case(matmul_add, [[[1, 2], [3, 4]], [[5, 6], [7, 8]], [[1, 1], [1, 1]]]).
case(sum_and_max, [[[1, 5], [4, 2]]]).
case(nested_sums, [[[[1, 2], [3, 4]], [[5, 6], [7, 8]]]]).
case(subtract_max, [[[1.0, 2.0], [3.0, 5.0]]]).
case(transpose, [[[1, 2], [3, 4]]]).
case(pad, [[1, 2]]).
case(shared, [[1, 2, 3]]).
case(float_reduce, [[[0.5, 1.5, 2.5], [3.5, 4.5, 5.5]]]).
case(flip_stride, [[[1, 2, 3, 4, 5], [6, 7, 8, 9, 10], [11, 12, 13, 14, 15]]]).
case(flip_pad, [[1, 2, 3]]).
case(where, [[-2.0, 1.0, -0.5, 3.0], [5.0, 6.0, 7.0, 8.0]]).
case(gather, [[[1.5, 2.5, 3.5], [4.5, 5.5, 6.5], [7.5, 8.5, 9.5]]]).
case(index_put, [[[1.5, 2.5, 3.5], [4.5, 5.5, 6.5], [7.5, 8.5, 9.5]], [0.5, 0.25]]).
case(index_put_arrays, [[[1.5, 2.5, 3.5], [4.5, 5.5, 6.5], [7.5, 8.5, 9.5]], [0.5, 0.25, 0.125]]).
case(scan, [[[1.0, 2.0], [3.0, 4.0], [5.0, 6.0]], [[0.5, 0.25], [0.0, 2.0]]]).

graph(chain, [A], C) :-
   C @= sin(A + A) * A.
graph(compare_wide, [A], C) :-
   C @= ((A * A) < 1000000000).
graph(round, [A], C) :-
   B @= A * 2.6,
   C = B.as(integer).
graph(matmul_add, [A, B, X], C) :-
   C @= (A @ B) + X.
graph(sum_and_max, [A], C) :-
   C @= A.sum([1]) + A.max([1]).
graph(nested_sums, [A], C) :-
   B @= A.sum([2]) * 2,
   C = B.sum([1]).
graph(subtract_max, [A], C) :-
   C @= A - A.max([1], true).
graph(transpose, [A], C) :-
   B @= A + A,
   C @= B.t() + A.
graph(pad, [A], C) :-
   B @= A + 1,
   C @= B.pad([1-1]) + 1.
graph(shared, [A], C) :-
   B @= A * A,
   C @= B + B.
graph(float_reduce, [A], C) :-
   B @= sqrt(A),
   C @= B.sum([0]) * 0.5.
graph(flip_stride, [A], C) :-
   C @= A.flip([1, 0]).stride([1, 2]) * 2.
graph(flip_pad, [A], C) :-
   C @= A.pad([2-0]).flip([1]) + 1.
graph(where, [A, B], C) :-
   C @= where(A > 0, sqrt(A), B * 2).
graph(gather, [A], C) :-
   C = A.index([[2, 0], [-1, 1]]).
graph(index_put, [A, V], C) :-
   C = A.index_put([sup:inf: -2, 1], V).
graph(index_put_arrays, [A, V], C) :-
   C = A.index_put([[2, 0, 2], [-1, 1, -1]], V).
graph(scan, [A, Mat], C) :-
   context_module(M),
   C = A.scanl(M:affine_sqrt(Mat), [0.0, 0.0], 0).

affine_sqrt(Mat, X, V0, V1) :-
   V1 @= Mat @ V0 + sqrt(X).

computed(Name, Device, List) :-
   case(Name, Inputs),
   maplist(input(Device), Inputs, Arrays),
   graph(Name, Arrays, C),
   List = C.tolist().

input(Device, List, A) :-
   A = array{}.fromlist(List, [device(Device)]).

% Floats may differ in their last bits: the device's sin, log or sqrt need
% not be Prolog's.
close_to(X, Y), is_list(X) =>
   maplist(close_to, X, Y).
close_to(X, Y), float(X) =>
   abs(X - Y) =< 1.0e-12 * max(1.0, abs(X)).
close_to(X, Y) =>
   X == Y.

test('same values as prolog', [forall((case(Name, _), opencl_device(Device, _)))]) :-
   computed(Name, prolog, Expected),
   computed(Name, opencl(Device), Values),
   close_to(Expected, Values).

% A float64 array on Device holding Values, which may hold NaN: ranges can't,
% so it starts as a C buffer, with an unbounded range.
float_array(Device, Values, A) :-
   length(Values, N),
   Data =.. [data | Values],
   buffer_from_data(Buffer, float64, N, Data),
   A0 = array{}.empty([N], [device(c), dtype(float), data(Buffer),
                            format(float64)]),
   A = A0.to(Device).

nan(X) :-
   float(X),
   float_class(X, nan).

test('a maximum propagates NaN', [forall(opencl_device(Name, _))]) :-
   current_prolog_flag(float_undefined, Undefined),
   setup_call_cleanup(set_prolog_flag(float_undefined, nan),
                      (  NaN is nan,
                         float_array(opencl(Name), [1.0, NaN, 3.0], A),
                         float_array(opencl(Name), [NaN, 1.0], B),
                         float_array(opencl(Name), [1.0, 3.0], C),
                         nan(A.max().tolist()),
                         nan(B.max().tolist()),
                         C.max().tolist() == 3.0
                      ),
                      set_prolog_flag(float_undefined, Undefined)).

test('rand fails loudly', [forall(opencl_device(Name, _))]) :-
   catch(_ = array{}.rand([2], [device(opencl(Name))]).tolist(), error(E, _), true),
   E == unsupported_op(opencl(Name), rand).

:- end_tests(opencl_kernel).
