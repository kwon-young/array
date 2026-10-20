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
array:M.compile(opencl(Name), float(A)) := Dict :-
   compile_kernel(Name, M, cast(A, M.dtype()), Dict).
array:M.compile(opencl(Name), integer(A)) := Dict :-
   integer_cast(A, M.dtype(), Expr),
   compile_kernel(Name, M, Expr, Dict).
array:M.compile(opencl(Name), Op) := Dict :-
   compile_kernel(Name, M, Op, Dict).

% compile_kernel(+Name, +M, +Expr, -Dict)
% Dict is M with a kernel storing the value of Expr at each index of M.
% The kernel runs one work item per element of M, which computes its index.
compile_kernel(Name, M, Expr, Dict) :-
   phrase(array:op_args(Expr), AllArgs),
   list_to_ord_set(AllArgs, Args),
   numlist_(M.ndim(), Numbers),
   maplist(atom_concat(i), Numbers, Index),
   Exprs = view{}.from_shape(M.shape()).reverse_index_expr(g),
   maplist([I, E, long:I = E]>>true, Index, Exprs, Declarations),
   kernel_body(opencl, M, Expr, Args, Index, Body),
   length(Args, NArgs),
   numlist(0, NArgs, ParamNumbers),
   maplist(param, [M | Args], ParamNumbers, Params),
   opt_level(Level),
   Code = kernel(Level, Params, Declarations, Body),
   % A kernel is named after its code, so a kernel already built is reused.
   variant_sha1(Code, Hash),
   atom_concat(kernel_, Hash, KernelName),
   load_kernel(Name, KernelName, Level, Code, Kernel),
   maplist([A, mem(Data)]>>get_dict(data, A, Data), [M | Args], KernelArgs),
   Dict = M.put(kernel, runtime_opencl:launch(Name, Kernel, KernelArgs, M.size())).

param(A, N, Type:Param) :-
   type_name(opencl, A.dtype(), Element),
   atomic_list_concat(['__global ', Element, '*'], Type),
   atom_concat(a, N, Param).

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
   Offset is M.view().offset * Size,
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

test('rand fails loudly', [forall(opencl_device(Name, _))]) :-
   catch(_ = array{}.rand([2], [device(opencl(Name))]).tolist(), error(E, _), true),
   E == unsupported_op(opencl(Name), rand).

:- end_tests(opencl_kernel).
