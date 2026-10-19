:- module(runtime_c, []).

:- use_module(array, []).
:- use_module(buffer).
:- use_module(c99).
:- use_module(swipl_ld).
:- use_module(gen_type).
:- use_module(view, [replace_nth0/4]).
:- use_module(dtype).
:- use_module(precision, [transfer_precision/3]).
:- use_module(fusion, [inlined_nodes//1, node_index/3, read_shape/2]).
:- use_module(library(clpBNR), []).

% Floats default to float64; integers and booleans take the smallest dtype
% holding their range.
array:default_format(c, M, Format) :-
   array:range_min_max(M.range, Min, Max),
   c_default_format(M.dtype, Min, Max, Format).
% Float formats that have a C type, smallest first.
array:float_formats(c, Formats) :-
   findall(F, (dtype_info(F, float, 0, 0, []), type(F, _, _, _)), Formats).
% Ops a C expression computes from its inputs.
array:expression_op(c, _+_).
array:expression_op(c, _*_).
array:expression_op(c, _<_).
array:expression_op(c, sin(_)).
array:expression_op(c, log(_)).
array:expression_op(c, sqrt(_)).
array:expression_op(c, float(_)).
array:expression_op(c, integer(_)).
array:expression_op(c, reduce(_, _, _)).
% Inlined floats are computed in the widest float format of the kernel.
array:compute_format(c, Formats, Format) :-
   widest_format(Formats, Format).

widest_format([], Format) =>
   Format = float64.
widest_format(Formats, Format) =>
   maplist(buffer_type_size, Formats, Sizes),
   pairs_keys_values(Pairs, Sizes, Formats),
   max_member(_-Format, Pairs).

array:M.dtype_size(c) := Size :-
   buffer_type_size(M.dtype(), Size).

% Compiles the operation for the given Array on the 'c' device.
array:M.compile(c, true) := Dict :-
   Dict = M.put(kernel, true).
array:M.compile(c, view(_)) := Dict :-
   Dict = M.put(kernel, true).
array:M.compile(c, constant(_)) := Dict :-
   Dict = M.put(kernel, true).
array:_M.compile(c, solve(_A, _B)) := _Dict :-
   throw(not_implemented).
array:M.compile(c, rand) := Dict :-
   type(M.dtype(), Type, _, _),
   compile_kernel(M, cast(rand(), Type) / 'RAND_MAX', Dict).
array:M.compile(c, float(A)) := Dict :-
   type(M.dtype(), Type, _, _),
   compile_kernel(M, cast(A, Type), Dict).
array:M.compile(c, integer(A)) := Dict :-
   type(M.dtype(), Type, _, _),
   integer_cast(A, Type, Expr),
   compile_kernel(M, Expr, Dict).
array:M.compile(c, Op) := Dict :-
   compile_kernel(M, Op, Dict).

% compile_kernel(+M, +Expr, -Dict)
% Dict is M with a kernel storing the value of Expr at each index of M.
compile_kernel(M, Expr, Dict) :-
   setup_kernel_call(M, Expr, Args, Index, Head, RuntimeName-Runtime),
   load_types(M, Expr, Args, LoadTypes),
   length(Args, NArgs),
   numlist_(NArgs, Numbers),
   maplist([Arg, N, Type, Arg-(Name-Type)]>>atom_concat(a, N, Name),
           Args, Numbers, LoadTypes, Pairs),
   list_to_assoc(Pairs, Loads),
   Ctx = ctx{index: Index, node: M, loads: Loads},
   phrase(value(Expr, Ctx, Value), Statements),
   foldl([S, C0, C]>>mkconj(C0, S, C), Statements, true, Body0),
   mkconj(Body0, a0[MIndexExpr] = Value, Body),
   c_index_expr(M, Index, MIndexExpr, MValidExpr),
   atom_string(RuntimeName, RuntimeStr),
   N is 1 + NArgs,
   AST = (
   #(include(<>, 'SWI-Prolog.h')),
   #(include(<>, 'stdint.h')),
   #(include(<>, 'stddef.h')),
   #(include(<>, 'stdbool.h')),
   #(include(<>, 'stdlib.h')),
   #(include(<>, 'math.h')),
   void:Head {
      if MValidExpr {
         Body
      }
   },
   Runtime,
   install_t:install(void) {
      'PL_register_foreign'(RuntimeStr, N, RuntimeName, 0)
   }
   ),
   name_variables(AST),
   once(phrase(translation_unit(AST), Tokens)),
   once(phrase(tokens(Tokens), Str)),
   clang_format(Str, In),
   compile_object(In, Object),
   link_objects([Object], Library),
   load_foreign_library(Library),
   maplist(get_dict(data), Args, Buffers),
   Buffer = M.data,
   Kernel =.. [RuntimeName, Buffer | Buffers],
   Dict = M.put([kernel=runtime_c:Kernel]).

numlist_(0, Numbers) =>
   Numbers = [].
numlist_(N, Numbers) =>
   numlist(1, N, Numbers).

% The C variables of a kernel are Prolog variables until it is printed.
name_variables(AST) :-
   term_variables(AST, Vars),
   foldl([Var, N0, N]>>(N is N0 + 1, atom_concat(t, N, Var)), Vars, 0, _).

ids(N, Prefix, Type, Args, TypeArgs) :-
   (  N == 0
   -> Numbers = []
   ;  numlist(1, N, Numbers)
   ),  
   maplist(atom_concat(Prefix), Numbers, Args),
   (  atom(Type)
   -> length(Types, N),
      maplist(=(Type), Types)
   ;  Types = Type,
      same_length(Args, Types)
   ),
   maplist([Type_, Arg, Type_:Arg]>>true, Types, Args, TypeArgs).
get_blob_data(Term, Type:Arg, Ast) :-
   Ast = (
      Type:Arg,
      'PL_get_blob'(Term, cast(&Arg, 'void**'), 'NULL', 'NULL')
   ).

setup_kernel_call(M, Op, UniqueArgs, Index, Head, RuntimeName-Runtime) :-
   ids(M.ndim(), i, int, Index, TypeIndex),
   phrase(array:op_args(Op), AllArgs),
   list_to_ord_set(AllArgs, UniqueArgs),
   length(UniqueArgs, NArgs),
   maplist(array:dtype, UniqueArgs, PrologDTypes),
   maplist(type, PrologDTypes, DTypes, _, _),
   maplist([DType, P]>>atom_concat(DType, *, P), DTypes, Ps),
   type(M.dtype(), MDType, _, _),
   atom_concat(MDType, *, Type),
   ids(NArgs, a, Ps, Args, TypeArgs),
   append(TypeArgs, TypeIndex, TypeArgsIndex),
   mapsubterms_var(clpBNR:domain, M, MDomain),
   variant_sha1(MDomain, KernelId),
   atom_concat('kernel_', KernelId, KernelName),
   Head =.. [KernelName, Type:a0 | TypeArgsIndex],
   append(Args, Index, ArgsIndex),
   Call =.. [KernelName, a0 | ArgsIndex],
   atom_concat('runtime_', KernelId, RuntimeName),
   ids(NArgs, t, term_t, Terms, TypeTerms),
   RuntimeHead =.. [RuntimeName, term_t:t0 | TypeTerms],
   maplist(get_blob_data, Terms, TypeArgs, BlobAstList),
   (  BlobAstList == []
   -> BlobAsts = true
   ;  comma_list(BlobAsts, BlobAstList)
   ),
   get_blob_data(t0, Type:a0, BlobAst),
   loops(M.shape(), TypeIndex, Call, LoopAst),
   Runtime = (
   'static foreign_t':RuntimeHead {
      BlobAst,
      BlobAsts,
      LoopAst,
      return('TRUE')
   }
   ).
loops([], [], Call, Call).
loops([Dim | Dims], TypeIndex, Call, Ast) :-
   loops_([Dim | Dims], TypeIndex, Call, Ast).

loops_([], [], Head, Head).
loops_([Dim | Dims], [Type:I | Index], Head, Ast) :-
   loops_(Dims, Index, Head, InnerAst),
   Ast = for(Type:I = 0, I < Dim, I++) {
      InnerAst
   }.
% Round like Prolog integer/1 instead of truncating like a C cast.
integer_cast(A, Type, Expr), operand_dtype(A, float) =>
   Expr = cast(round(A), Type).
integer_cast(A, Type, Expr) =>
   Expr = cast(A, Type).

% C evaluates an operation in the type of its operands, so loading each input
% in its own type makes e.g. uint32 * uint32 wrap before being stored as
% uint64, or compares uint32 < int8 as unsigned.
% Instead, load every input in the smallest type that holds all inputs and,
% for arithmetic, the result too.
% A cast must see its input unchanged, so it keeps the input's own type.
% An inlined node is held in its own format, so the compute type must hold
% its range too.
load_types(_M, cast(A, _), Args, Types), is_dict(A, array) =>
   maplist(array:dtype, Args, DTypes),
   maplist(type, DTypes, Types, _, _).
load_types(_M, A<B, Args, Types) =>
   phrase(inlined_nodes(A<B), Inlined),
   append(Inlined, Args, Arrays),
   same_compute_type(Arrays, Args, Types).
load_types(M, Op, Args, Types) =>
   phrase(inlined_nodes(Op), Inlined),
   append([M | Inlined], Args, Arrays),
   same_compute_type(Arrays, Args, Types).

same_compute_type(Arrays, Args, Types) :-
   compute_dtype(Arrays, DType),
   type(DType, Type, _, _),
   same_length(Args, Types),
   maplist(=(Type), Types).

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

% value(+Expr, +Ctx, -Value)//
% The statements computing Value, the value of Expr at the index of Ctx.
% Ctx also holds the node being computed, and the name and load type of each
% buffer the kernel reads.
value(A, Ctx, Value), is_dict(A, array) ==>
   load(A, Ctx, Value).
% An inlined node is rounded to its format, as its buffer would be.
value(fused(Node, Expr), Ctx, Value) ==>
   value(Expr, Ctx.put(node, Node), Value0),
   { type(Node.dtype(), Type, _, _) },
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
value(cast(A, Type), Ctx, Value) ==>
   value(A, Ctx, Value0),
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
   {  type(Ctx.node.dtype(), Type, _, _),
      array:identity(Op, Identity0),
      c_identity(Ctx.node.dtype(), Identity0, Identity),
      read_shape(Parent, Shape),
      maplist([Axis, Dim]>>nth0(Axis, Shape, Dim), Axes, Dims),
      same_length(Axes, Js),
      foldl(replace_nth0, Js, Axes, Ctx.index, Index),
      phrase(value(Parent, Ctx.put(index, Index), V), Body0),
      accumulate(Op, Acc, Item, Update),
      append(Body0, [Type:Item = V, Update], Body1),
      foldl([S, C0, C]>>mkconj(C0, S, C), Body1, true, Body),
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

% Allocates the physical memory or underlying data storage for Array on the 'c' device.
array:allocate(c, M) :-
    buffer_alloc(M.data, M.dtype(), M.datasize, true).

% Defines the type promotion rules on the 'c' device.
% array:broadcast_dtype(c, int64, int64).

array:M.to(c, prolog) := Dict :-
   M1 = M.contiguous().realize(),
   buffer_to_data(M1.data, M1.dtype(), M1.datasize, Data),
   % prolog floats hold every C value exactly
   Dict = M.empty(M1.shape(), [device(prolog), data(Data), precision(M1.precision)]).

array:M.to(prolog, c) := Dict :-
   M1 = M.contiguous().realize(),
   Copy = M.empty(M1.shape(), [device=c, data(Data)]),
   transfer_precision(M1, Copy, Dict),
   array:bind_default_format(Dict),
   buffer_from_data(Data, Dict.dtype(), M1.datasize, M1.data).

c_identity(int8, -inf, 'INT8_MIN').
c_identity(int16, -inf, 'INT16_MIN').
c_identity(int32, -inf, 'INT32_MIN').
c_identity(int64, -inf, 'INT64_MIN').
c_identity(integer, -inf, 'INT64_MIN').
c_identity(uint8, -inf, 0).
c_identity(uint16, -inf, 0).
c_identity(uint32, -inf, 0).
c_identity(uint64, -inf, 0).
c_identity(float16, -inf, '-INFINITY').
c_identity(float32, -inf, '-INFINITY').
c_identity(float64, -inf, '-INFINITY').
c_identity(float, -inf, '-INFINITY').
c_identity(bool, -inf, 0).
c_identity(boolean, -inf, 0).
c_identity(_, Identity, Identity) :-
   number(Identity).
