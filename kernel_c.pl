:- module(kernel_c, [
   kernel_body/6,
   opt_level/1,
   statements/2,
   integer_cast/3,
   type_name/3,
   c_default_format/4,
   loops/4,
   name_variables/1,
   numlist_/2
]).

/** <module> C-family kernels

The body of a kernel in C or OpenCL C, the dialects: the statements storing
the value of an expression at one index of the array it computes.

Types are formats, such as int32 or float64, until type_name/3 names them in
a dialect.
*/

:- use_module(library(assoc)).
:- use_module(library(dcg/high_order)).
:- use_module(c99).
:- use_module(array, []).
:- use_module(buffer, [buffer_type_size/2]).
:- use_module(dtype, [dtype_info/5]).
:- use_module(gen_type, [type/4]).
:- use_module(view, [replace_nth0/4]).
:- use_module(fusion, [inlined_nodes//1, node_index/3, read_shape/2]).

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

% kernel_body(+Dialect, +M, +Expr, +Args, +Index, -Body)
% Body stores in a0 the value of Expr at Index of M, loading Args from a1,
% a2...
kernel_body(Dialect, M, Expr, Args, Index, Body) :-
   load_types(M, Expr, Args, Formats),
   maplist(type_name(Dialect), Formats, Types),
   length(Args, NArgs),
   numlist_(NArgs, Numbers),
   maplist([Arg, N, Type, Arg-(Name-Type)]>>atom_concat(a, N, Name),
           Args, Numbers, Types, Pairs),
   list_to_assoc(Pairs, Loads),
   Ctx = ctx{dialect: Dialect, index: Index, node: M, loads: Loads},
   phrase(value(Expr, Ctx, Value), Statements),
   c_index_expr(M, Index, MIndexExpr, MValidExpr),
   append(Statements, [a0[MIndexExpr] = Value], Statements1),
   statements(Statements1, Store),
   Body = if MValidExpr { Store }.

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

identity(Dialect, Format, -inf, Identity) =>
   lowest(Dialect, Format, Identity).
identity(_, _, Identity0, Identity) =>
   Identity = Identity0.

% Formats
% =======

% Round like Prolog integer/1 instead of truncating like a C cast.
integer_cast(A, Format, Expr), operand_dtype(A, float) =>
   Expr = cast(round(A), Format).
integer_cast(A, Format, Expr) =>
   Expr = cast(A, Format).

% C evaluates an operation in the type of its operands, so loading each input
% in its own type makes e.g. uint32 * uint32 wrap before being stored as
% uint64, or compares uint32 < int8 as unsigned.
% Instead, load every input in the smallest format that holds all inputs
% and, for arithmetic, the result too.
% A cast must see its input unchanged, so it keeps the input's own format.
% An inlined node is held in its own format, so the compute format must hold
% its range too.
load_types(_M, cast(A, _), Args, Formats), is_dict(A, array) =>
   maplist(array:dtype, Args, Formats).
load_types(_M, A<B, Args, Formats) =>
   phrase(inlined_nodes(A<B), Inlined),
   append(Inlined, Args, Arrays),
   same_compute_format(Arrays, Args, Formats).
load_types(M, Op, Args, Formats) =>
   phrase(inlined_nodes(Op), Inlined),
   append([M | Inlined], Args, Arrays),
   same_compute_format(Arrays, Args, Formats).

same_compute_format(Arrays, Args, Formats) :-
   compute_dtype(Arrays, Format),
   same_length(Args, Formats),
   maplist(=(Format), Formats).

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

% Values
% ======

% value(+Expr, +Ctx, -Value)//
% The statements computing Value, the value of Expr at the index of Ctx.
% Ctx also holds the dialect, the node being computed, and the name and load
% type of each buffer the kernel reads.
value(A, Ctx, Value), is_dict(A, array) ==>
   load(A, Ctx, Value).
% An inlined node is rounded to its format, as its buffer would be.
value(fused(Node, Expr), Ctx, Value) ==>
   value(Expr, Ctx.put(node, Node), Value0),
   { type_name(Ctx.dialect, Node.dtype(), Type) },
   { Value = cast(Value0, Type) }.
% Expr is computed at the index of the node that Via reads.
value(reindex(Via, Expr), Ctx, Value) ==>
   { node_index(Via, Ctx.index, Index) },
   value(Expr, Ctx.put(index, Index), Value).
value(reduce(Op, Axes, Parent), Ctx, Value) ==>
   reduction(Op, Axes, Parent, Ctx, Value).
value(contiguous(A), Ctx, Value) ==>
   value(A, Ctx, Value).
% The cast is the one of fused/2.
value(float(A), Ctx, Value) ==>
   value(A, Ctx, Value).
value(integer(A), Ctx, Value), operand_dtype(A, float) ==>
   value(A, Ctx, Value0),
   { Value = round(Value0) }.
value(integer(A), Ctx, Value) ==>
   value(A, Ctx, Value).
value(cast(A, Format), Ctx, Value) ==>
   value(A, Ctx, Value0),
   { type_name(Ctx.dialect, Format, Type) },
   { Value = cast(Value0, Type) }.
value(Atom, _, Value), atom(Atom) ==>
   { Value = Atom }.
value(Op, Ctx, Value), compound(Op) ==>
   { compound_name_arguments(Op, Name, Args) },
   values(Args, Ctx, Values),
   { compound_name_arguments(Value, Name, Values) }.

values([], _, Values) ==>
   { Values = [] }.
values([A | As], Ctx, Values) ==>
   value(A, Ctx, V),
   values(As, Ctx, Vs),
   { Values = [V | Vs] }.

load(A, Ctx, Value) -->
   {  get_assoc(A, Ctx.loads, Name-Type),
      c_index_expr(A, Ctx.index, IndexExpr, ValidExpr),
      (  array:skip_view(A.op, constant(Constant))
      -> Load = (Value = Constant)
      ;  Load = (Value = Name[IndexExpr])
      )
   },
   [  Type:Value = 0,
      if ValidExpr {
         Load
      }
   ].

% A reduction of Ctx's node accumulates, in the node's type, the values of
% Parent at each index that the reduced axes add to the node's index.
reduction(Op, Axes, Parent, Ctx, Acc) -->
   {  Format = Ctx.node.dtype(),
      type_name(Ctx.dialect, Format, Type),
      array:identity(Op, Identity0),
      identity(Ctx.dialect, Format, Identity0, Identity),
      read_shape(Parent, Shape),
      maplist([Axis, Dim]>>nth0(Axis, Shape, Dim), Axes, Dims),
      same_length(Axes, Js),
      foldl(replace_nth0, Js, Axes, Ctx.index, Index),
      phrase(value(Parent, Ctx.put(index, Index), V), Body0),
      accumulate(Op, Acc, Item, Update),
      append(Body0, [Type:Item = V, Update], Body1),
      statements(Body1, Body),
      maplist([J, int:J]>>true, Js, TypedJs),
      loops(Dims, TypedJs, Body, Loop)
   },
   [Type:Acc = Identity, Loop].

accumulate(<, Acc, Item, Update) =>
   Update = if(Acc < Item) { Acc = Item }.
accumulate(Op, Acc, Item, Update) =>
   Expr =.. [Op, Acc, Item],
   Update = (Acc = Expr).

operand_dtype(fused(Node, _), DType) =>
   DType = Node.dtype.
operand_dtype(A, DType) =>
   DType = A.dtype.

% index_expr/1 gives the validity of an index as a Prolog goal: C spells its
% conjunction &&.
c_index_expr(M, Index, IndexExpr, ValidExpr) :-
   IndexExpr-Valid = M.index_expr(Index),
   c_condition(Valid, ValidExpr).

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
