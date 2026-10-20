:- module(kernel_c, [
   lowest/3,
   reduction_hint/4,
   loops/5,
   c_condition/2,
   opt_level/1,
   statements/2,
   type_name/3,
   compute_dtype/2,
   c_default_format/4,
   loops/4,
   name_variables/1,
   numlist_/2
]).

/** <module> C-family kernels

What the C and OpenCL C dialects share: the optimization level of their
compilers, the names of formats in each dialect, the identity of a maximum,
the reduction hints, the formats kernels compute in, and the pieces of C
syntax their printers build (loops, conditions, statements).

Types are formats, such as int32 or float64, until type_name/3 names them in
a dialect.
*/

:- use_module(c99).
:- use_module(array, []).
:- use_module(buffer, [buffer_type_size/2]).
:- use_module(dtype, [dtype_info/5]).
:- use_module(gen_type, [type/4]).

% The optimization level of the kernel compilers, from 0 to 3: the
% environment variable ARRAY_OPT, or 2. Set the array_opt flag to change it.
env_opt_level(Level), getenv('ARRAY_OPT', Value), atom_number(Value, Level0) =>
   Level = Level0.
env_opt_level(_), getenv('ARRAY_OPT', Value) =>
   type_error(integer, Value).
env_opt_level(Level) =>
   Level = 2.

:- env_opt_level(Level),
   create_prolog_flag(array_opt, Level, [type(integer), keep(true)]).

opt_level(Level) :-
   current_prolog_flag(array_opt, Level),
   must_be(between(0, 3), Level).

statements(List, Statements) :-
   foldl([S, C0, C]>>mkconj(C0, S, C), List, true, Statements).

numlist_(0, Numbers) =>
   Numbers = [].
numlist_(N, Numbers) =>
   numlist(1, N, Numbers).

% The C variables of a kernel are Prolog variables until it is printed.
name_variables(AST) :-
   term_variables(AST, Vars),
   foldl([Var, N0, N]>>(N is N0 + 1, atom_concat(t, N, Var)), Vars, 0, _).

loops([], [], Call, Call).
loops([Dim | Dims], TypeIndex, Call, Ast) :-
   loops_([Dim | Dims], TypeIndex, Call, Ast).

% loops(+Dims, +TypeIndex, +Body, +Hint, -Ast)
% Ast loops over Dims, with the statement Hint before the innermost loop.
loops([Dim], [Type:I], Body, Hint, Ast) =>
   mkconj(Hint, for(Type:I = 0, I < Dim, I++) { Body }, Ast).
loops([Dim | Dims], [Type:I | Index], Body, Hint, Ast) =>
   loops(Dims, Index, Body, Hint, InnerAst),
   Ast = for(Type:I = 0, I < Dim, I++) {
      InnerAst
   }.

loops_([], [], Head, Head).
loops_([Dim | Dims], [Type:I | Index], Head, Ast) :-
   loops_(Dims, Index, Head, InnerAst),
   Ast = for(Type:I = 0, I < Dim, I++) {
      InnerAst
   }.

% Dialects
% ========

% type_name(?Dialect, ?Format, ?Name)
type_name(c, Format, Name) :-
   type(Format, Name, _, _).
type_name(opencl, Format, Name) :-
   opencl_type(Format, Name).

% OpenCL C has no bool in buffers: a boolean is stored in a byte.
opencl_type(bool, uchar).
opencl_type(int8, char).
opencl_type(uint8, uchar).
opencl_type(int16, short).
opencl_type(uint16, ushort).
opencl_type(int32, int).
opencl_type(uint32, uint).
opencl_type(int64, long).
opencl_type(uint64, ulong).
opencl_type(float16, half).
opencl_type(float32, float).
opencl_type(float64, double).

% reduction_hint(+Dialect, +Op, +Acc, -Hint)
% Hint lets the compiler reorder a reduction into Acc, for example into SIMD
% lanes. A sum may be reordered: its error bound holds for any summation
% order (see precision.pl). A maximum may not: with NaNs, the order changes
% the result.
reduction_hint(c, +, Acc, Hint) =>
   Hint = pragma([omp, simd, reduction(+, Acc)]).
reduction_hint(_, _, _, Hint) =>
   Hint = true.

% lowest(?Dialect, ?Format, ?Constant): the identity of a maximum.
lowest(c, int8, 'INT8_MIN').
lowest(c, int16, 'INT16_MIN').
lowest(c, int32, 'INT32_MIN').
lowest(c, int64, 'INT64_MIN').
lowest(opencl, int8, 'CHAR_MIN').
lowest(opencl, int16, 'SHRT_MIN').
lowest(opencl, int32, 'INT_MIN').
lowest(opencl, int64, 'LONG_MIN').
lowest(_, uint8, 0).
lowest(_, uint16, 0).
lowest(_, uint32, 0).
lowest(_, uint64, 0).
lowest(_, bool, 0).
lowest(_, float16, '-INFINITY').
lowest(_, float32, '-INFINITY').
lowest(_, float64, '-INFINITY').

% Formats
% =======

% compute_dtype(+Arrays, -DType)
% C evaluates an operation in the type of its operands, so loading each input
% in its own type makes e.g. uint32 * uint32 wrap before being stored as
% uint64, or compares uint32 < int8 as unsigned. Instead, kernels load every
% input in DType, the smallest format that holds all of Arrays: the inputs,
% the inlined nodes and, for arithmetic, the result.
compute_dtype(Arrays, DType) :-
   maplist(get_dict(dtype), Arrays, Kinds),
   foldl(array:broadcast_dtype, Kinds, boolean, Kind),
   compute_dtype(Kind, Arrays, DType).

% Floats compute in the widest float format among the arrays.
compute_dtype(float, Arrays, DType) =>
   include([A]>>get_dict(dtype, A, float), Arrays, Floats),
   maplist(array:dtype, Floats, Formats),
   maplist(buffer_type_size, Formats, Sizes),
   pairs_keys_values(Pairs, Sizes, Formats),
   max_member(_-DType, Pairs).
compute_dtype(Kind, Arrays, DType) =>
   maplist(get_dict(range), Arrays, Ranges),
   maplist(array:range_min_max, Ranges, Mins, Maxs),
   min_list(Mins, Min),
   max_list(Maxs, Max),
   c_dtype(Kind, Min, Max, DType).

c_default_format(float, _Min, _Max, Format) =>
   Format = float64.
c_default_format(Kind, Min, Max, Format) =>
   c_dtype(Kind, Min, Max, Format).

% An unbounded range only says that the values are unknown, so no dtype can be
% proven to hold them: fall back to the default dtype of the kind instead.
c_dtype(Kind, Min, Max, DType), unbounded(Min, Max) =>
   default_dtype(Kind, DType).
c_dtype(Kind, Min, Max, DType),
      once(dtype_info(DType0, Kind, Min, Max, [])) =>
   DType = DType0.
c_dtype(Kind, Min, Max, _DType) =>
   existence_error(c_dtype, dtype(Kind, Min, Max)).

unbounded(-1.0Inf, _).
unbounded(_, 1.0Inf).

default_dtype(boolean, bool).
default_dtype(integer, int64).

c_condition((A, B), Condition) =>
   c_condition(A, A1),
   c_condition(B, B1),
   Condition = (A1 && B1).
c_condition(Goal, Condition) =>
   Condition = Goal.

:- begin_tests(kernel_opt).

:- use_module(array).

with_opt_level(Level, Goal) :-
   current_prolog_flag(array_opt, Old),
   setup_call_cleanup(set_prolog_flag(array_opt, Level),
                      Goal,
                      set_prolog_flag(array_opt, Old)).

% The kernel computing A + A.
double_kernel(Device, Kernel) :-
   A = array{}.fromlist([1.5, 2.5], [device(Device)]),
   B @= A + A,
   array:create_schedule([B], Schedule),
   last(Schedule, Node),
   array:compile(Node, Compiled),
   Kernel = Compiled.kernel.

kernel_device(c).
kernel_device(opencl(Name)) :-
   opencl:opencl_device(Name, _).

test('the level builds its own kernel', [forall(kernel_device(Device))]) :-
   with_opt_level(0, double_kernel(Device, Kernel0)),
   with_opt_level(2, double_kernel(Device, Kernel2)),
   Kernel0 \== Kernel2.

matmul_add(Device, List) :-
   A = array{}.fromlist([[1, 2], [3, 4]], [device(Device)]),
   C @= (A @ A) + A,
   List = C.tolist().

test('every level computes the same values', [forall(kernel_device(Device))]) :-
   forall(between(0, 3, Level),
          (  with_opt_level(Level, matmul_add(Device, List)),
             List == [[8, 12], [18, 26]]
          )).

test('a level outside 0..3 fails loudly',
     [throws(error(type_error(between(0, 3), 7), _))]) :-
   with_opt_level(7, double_kernel(c, _)).

:- end_tests(kernel_opt).
