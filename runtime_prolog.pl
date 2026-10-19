:- module(runtime_prolog, []).

:- use_module(library(dcg/high_order)).
:- use_module(array, []).
:- use_module(view, [replace_nth0/4]).
:- use_module(lu_decomposition).
:- use_module(fusion, [node_index/3, read_shape/2]).

/* 
 * Runtime Backend Interface
 * =========================
 * To be used by array.pl, a runtime backend (device) must implement the
 * following multifile predicates in the `array` module:
 *
 * - array:compile(Device, Op, Array, CompiledDict)
 *   (Often implemented via dict method: array:Array.compile(Device, Op) := CompiledDict)
 *   Compiles the operation `Op` for the given `Array` on `Device`. 
 *   Returns a new dict containing at least a `kernel` key with a callable goal 
 *   that performs the operation.
 *
 * - array:allocate(Device, Array)
 *   Allocates the physical memory or underlying data storage for `Array` on `Device`.
 *   Typically binds the `data` field of the Array dict.
 *
 * - array:dtype(Device, Value, DType)
 *   Maps a Prolog `Value` to its corresponding data type representation (e.g., 
 *   boolean, integer, float) supported by the backend on `Device`.
 *
 * - array:broadcast_dtype(Device, DType1, DType2)
 *   Defines the type promotion rules. It should succeed if `DType1` can be 
 *   safely broadcast/promoted to `DType2` on the given `Device`.
 */

array:_M.dtype_size(prolog) := 1 :-
   true.

% Prolog floats are doubles; integers and booleans are exact.
array:default_format(prolog, M, Format) :-
   prolog_format(M.dtype, Format).

prolog_format(float, Format) =>
   Format = float64.
prolog_format(Kind, Format) =>
   Format = Kind.

array:float_formats(prolog, [float64]).

% Ops a Prolog kernel computes from its inputs.
array:expression_op(prolog, _+_).
array:expression_op(prolog, _*_).
array:expression_op(prolog, _<_).
array:expression_op(prolog, sin(_)).
array:expression_op(prolog, log(_)).
array:expression_op(prolog, sqrt(_)).
array:expression_op(prolog, float(_)).
array:expression_op(prolog, integer(_)).
array:expression_op(prolog, reduce(_, _, _)).
array:compute_format(prolog, _, float64).

array:M.compile(prolog, true) := Dict :-
   Dict = M.put(kernel, true).
array:M.compile(prolog, view(_)) := Dict :-
   Dict = M.put(kernel, true).
array:M.compile(prolog, constant(_)) := Dict :-
   Dict = M.put(kernel, true).
array:M.compile(prolog, solve(A, B)) := Dict :-
    [N, N] = A.shape(),
    (  B.shape() = [N, M_]
    -> true
    ;  B.shape() = [N], M_ = 1
    ),
    OffsetA = A.view().offset,
    OffsetB = B.view().offset,
    OffsetX = M.view().offset,
    Dict = M.put(kernel,
                 lu_decomposition:solve(A.data, OffsetA,
                                        B.data, OffsetB,
                                        N, M_, M.data, OffsetX)).
array:M.compile(prolog, rand) := Dict :-
   compile_kernel(M, random_float, Dict).
array:M.compile(prolog, Op) := Dict :-
   compile_kernel(M, Op, Dict).

% compile_kernel(+M, +Expr, -Dict)
% Dict is M with a kernel storing the value of Expr at each index of M.
% The kernel is a clause of the kernel module, whose parameters are the
% data of M, the data of each array Expr reads, and the index.
compile_kernel(M, Expr, Dict) :-
   length(Index, M.ndim()),
   phrase(array:op_args(Expr), AllArgs),
   list_to_ord_set(AllArgs, Args),
   phrase(value(Expr, ctx{index: Index}, Value), Goals),
   conjunction(Goals, Body0),
   MIndexExpr-MValidExpr = M.index_expr(Index),
   Body = (
      Body0,
      (  MValidExpr
      -> MValue is Value,
         MIndex is MIndexExpr+1,
         nb_setarg(MIndex, M.id, MValue)
      ;  true
      )
   ),
   maplist(get_dict(id), Args, Ids),
   append([M.id | Ids], Index, Params),
   % A kernel is named after its code, so a kernel already defined is reused.
   variant_sha1(Params-Body, KernelId),
   Head =.. [KernelId | Params],
   define_kernel(Head, Body),
   maplist(get_dict(data), Args, Datas),
   append([M.data | Datas], Index, CallArgs),
   Call =.. [KernelId | CallArgs],
   maplist([Dim, I, between(0, Dim1, I)]>>(Dim1 is Dim-1), M.shape(), Index, L),
   conjunction(L, Betweens),
   Dict = M.put([kernel=forall(Betweens, kernel:Call)]).

define_kernel(Head, _), functor(Head, Name, Arity),
      current_predicate(kernel:Name/Arity) =>
   true.
define_kernel(Head, Body) =>
   assertz((kernel:Head :- Body)).

conjunction(Goals, Conjunction) :-
   foldl([G, C0, C]>>mkconj(C0, G, C), Goals, true, Conjunction).

% value(+Expr, +Ctx, -Value)//
% The goals computing Value, an arithmetic expression for the value of Expr
% at the index of Ctx.
value(A, Ctx, Value), is_dict(A, array) ==>
   { Goal-Value = A.index_input(Ctx.index) },
   [Goal].
value(fused(_Node, Expr), Ctx, Value) ==>
   value(Expr, Ctx, Value).
% Expr is computed at the index of the node that Via reads.
value(reindex(Via, Expr), Ctx, Value) ==>
   { node_index(Via, Ctx.index, Index) },
   value(Expr, Ctx.put(index, Index), Value).
value(reduce(Op, Axes, Parent), Ctx, Value) ==>
   reduction(Op, Axes, Parent, Ctx, Value).
value(contiguous(A), Ctx, Value) ==>
   value(A, Ctx, Value).
% Prolog arithmetic has no comparison function.
value(A<B, Ctx, Value) ==>
   value(A, Ctx, A1),
   value(B, Ctx, B1),
   [(A1 < B1 -> Value = 1 ; Value = 0)].
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

% A reduction accumulates the values of Parent at each index that the reduced
% axes add to Ctx's index.
reduction(Op, Axes, Parent, Ctx, Value) -->
   {  array:identity(Op, Identity),
      read_shape(Parent, Shape),
      same_length(Axes, Js),
      foldl(replace_nth0, Js, Axes, Ctx.index, Index),
      maplist([Axis, J, between(0, Max, J)]>>(nth0(Axis, Shape, Dim), Max is Dim - 1),
              Axes, Js, Betweens0),
      conjunction(Betweens0, Betweens),
      phrase(value(Parent, Ctx.put(index, Index), Item), Body0),
      accumulate(Op, Acc, Item, Update),
      append(Body0, [Update], Body1),
      conjunction(Body1, Body)
   },
   [  Acc = acc(_),
      nb_setarg(1, Acc, Identity),
      forall(Betweens, Body),
      arg(1, Acc, Value)
   ].

accumulate(<, Acc, Item, Update) =>
   Update = (
      arg(1, Acc, A0),
      V is Item,
      (  A0 < V
      -> nb_setarg(1, Acc, V)
      ;  true
      )
   ).
accumulate(Op, Acc, Item, Update) =>
   Expr =.. [Op, A0, Item],
   Update = (
      arg(1, Acc, A0),
      V is Expr,
      nb_setarg(1, Acc, V)
   ).

array:allocate(prolog, M) :-
   compound_name_arity(M.data, data, M.datasize).

% DTypes
% ======
% array:dtype(prolog, 0, R) => R = boolean.
% array:dtype(prolog, 1, R) => R = boolean.
% array:dtype(prolog, X, R), float(X) => R = float.
% array:dtype(prolog, X, R), integer(X) => R = integer.
% array:dtype(prolog, X, R), rational(X) => R = rational.
% array:dtype(prolog, X, DType), var(X) => when(ground(X), array:dtype(prolog, X, DType)).
%
% array:broadcast_dtype(prolog, boolean, integer).
% array:broadcast_dtype(prolog, integer, rational).
% array:broadcast_dtype(prolog, rational, float).
