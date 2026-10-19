:- module(runtime_prolog, [op_expr/3]).

:- use_module(library(dcg/high_order)).
:- use_module(array, []).
:- use_module(view, [replace_nth0/4]).
:- use_module(lu_decomposition).
:- use_module(library(clpBNR), [domain/2]).

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

% Ops Prolog arithmetic computes from its inputs: it has no comparison
% function, so a comparison can only be the outermost op of a kernel.
array:expression_op(prolog, _+_).
array:expression_op(prolog, _*_).
array:expression_op(prolog, sin(_)).
array:expression_op(prolog, log(_)).
array:expression_op(prolog, sqrt(_)).
array:expression_op(prolog, float(_)).
array:expression_op(prolog, integer(_)).
array:compute_format(prolog, _, float64).

setup_kernel_call(M, Args, Index, ModuleHead, Dict) :-
   mapsubterms_var(domain, M, MDomain),
   variant_sha1(MDomain, KernelId),
   maplist(get_dict(id), Args, Ids),
   append(Ids, Index, IdsIndex),
   Head =.. [KernelId, M.id | IdsIndex],
   ModuleHead = kernel:Head,

   maplist(get_dict(data), Args, Datas),
   append(Datas, Index, DatasIndex),
   CallHead =.. [KernelId, M.data | DatasIndex],
   maplist([Dim, I, between(0, Dim1, I)]>>(Dim1 is Dim-1), M.shape(), Index, L),
   (  L = []
   -> Betweens = true
   ;  comma_list(Betweens, L)
   ),
   Dict = M.put([kernel=forall(Betweens, (kernel:CallHead))]).

compile_expr(Op, Args, Index, Value, AST) :-
   % index inputs
   maplist(array:index_input(Index), Args, Pairs),
   pairs_keys_values(Pairs, ASTs, Values),
   foldl(mkconj, ASTs, true, BaseAST),

   % inline elementwise op using op_expr
   pairs_keys_values(PairsForRbtree, Args, Values),
   ord_list_to_rbtree(PairsForRbtree, ArgTree),
   op_expr(Op, Expr, ArgTree),

   % evaluate the expression, handling comparisons
   (  compound(Expr), Expr =.. [<|_]
   -> EvalAST = (Expr -> Value = 1; Value = 0)
   ;  EvalAST = (Value is Expr)
   ),
   mkconj(BaseAST, EvalAST, AST).

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
   Dict = M.compile(prolog, elementwise(random_float)).
array:M.compile(prolog, contiguous(Parent)) := Dict :-
   Dict = M.compile(prolog, elementwise(contiguous(Parent))).
array:M.compile(prolog, A<B) := Dict :-
   Dict = M.compile(prolog, elementwise(A<B)).
array:M.compile(prolog, A+B) := Dict :-
   Dict = M.compile(prolog, elementwise(A+B)).
array:M.compile(prolog, A*B) := Dict :-
   Dict = M.compile(prolog, elementwise(A*B)).
array:M.compile(prolog, sin(A)) := Dict :-
   Dict = M.compile(prolog, elementwise(sin(A))).
array:M.compile(prolog, log(A)) := Dict :-
   Dict = M.compile(prolog, elementwise(log(A))).
array:M.compile(prolog, sqrt(A)) := Dict :-
   Dict = M.compile(prolog, elementwise(sqrt(A))).
array:M.compile(prolog, float(A)) := Dict :-
   Dict = M.compile(prolog, elementwise(float(A))).
array:M.compile(prolog, integer(A)) := Dict :-
   Dict = M.compile(prolog, elementwise(integer(A))).
array:M.compile(prolog, elementwise(Op)) := Dict :-
   length(Index, M.ndim()),
   phrase(array:op_args(Op), AllArgs),
   list_to_ord_set(AllArgs, Args),
   setup_kernel_call(M, Args, Index, ModuleHead, Dict),

   compile_expr(Op, Args, Index, MValue, Body),

   % index output
   MIndexExpr-MValidExpr = M.index_expr(Index),

   % Head :- Body
   Kernel = (ModuleHead :-
      Body,
      (  MValidExpr
      -> MIndex is MIndexExpr+1,
         nb_setarg(MIndex, M.id, MValue)
      ;  true
      )
   ),
   retractall(ModuleHead),
   asserta(Kernel).
array:M.compile(prolog, reduce(Op, Axes, Parent)) := Dict :-
   length(Index, M.ndim()),
   phrase(array:op_args(Parent), AllArgs),
   list_to_ord_set(AllArgs, Args),
   setup_kernel_call(M, Args, Index, ModuleHead, Dict),

   same_length(Axes, AccIndex),
   foldl(replace_nth0, AccIndex, Axes, Index, FullIndex),

   compile_expr(Parent, Args, FullIndex, ParentValue, ParentAST),

   MIndexExpr-MValidExpr = M.index_expr(Index),
   AccExpr =.. [Op, AccValue, ParentValue],
   array:identity(Op, Identity),
   (  Op = (<)
   -> NewAccExpr = (
      (  AccExpr
      -> NewAccValue = ParentValue
      ;  NewAccValue = AccValue
      ))
   ;  NewAccExpr = (NewAccValue is AccExpr)
   ),
   mkconj(ParentAST, (
      arg(1, Acc, AccValue),
      NewAccExpr,
      nb_setarg(1, Acc, NewAccValue)),
      AccAST),
   [Arg0|_] = Args,
   ParentShape = Arg0.shape(),
   maplist({ParentShape}/[Axis, I, between(0, Dim1, I)]>>(
           nth0(Axis, ParentShape, Dim), Dim1 is Dim-1),
           Axes, AccIndex, BList),
   comma_list(Betweens, BList),
   Kernel = (ModuleHead :-
      Acc = acc(Identity, _),
      forall(Betweens, AccAST),
      arg(1, Acc, MValue),
      (  MValidExpr
      -> MIndex is MIndexExpr+1,
         nb_setarg(MIndex, M.id, MValue)
      ;  true
      )
   ),
   retractall(ModuleHead),
   asserta(Kernel).

op_expr(random_float, R, _) =>
   R = random_float.
op_expr(A, R, Index), is_dict(A, array) =>
   rb_lookup(A, R, Index).
op_expr(contiguous(A), R, Index) =>
   op_expr(A, R, Index).
op_expr(fused(_Node, Expr), R, Index) =>
   op_expr(Expr, R, Index).
op_expr(A+B, R, Index) =>
   op_expr(A, A1, Index),
   op_expr(B, B1, Index),
   R = (A1+B1).
op_expr(A*B, R, Index) =>
   op_expr(A, A1, Index),
   op_expr(B, B1, Index),
   R = (A1*B1).
op_expr(A<B, R, Index) =>
   op_expr(A, A1, Index),
   op_expr(B, B1, Index),
   R = (A1<B1).
op_expr(sin(A), R, Index) =>
   op_expr(A, A1, Index),
   R = sin(A1).
op_expr(log(A), R, Index) =>
   op_expr(A, A1, Index),
   R = log(A1).
op_expr(sqrt(A), R, Index) =>
   op_expr(A, A1, Index),
   R = sqrt(A1).
op_expr(float(A), R, Index) =>
   op_expr(A, A1, Index),
   R = float(A1).
op_expr(integer(A), R, Index) =>
   op_expr(A, A1, Index),
   R = integer(A1).

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
