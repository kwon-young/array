:- module(runtime_prolog, []).

:- use_module(library(dcg/high_order)).
:- use_module(array, []).
:- use_module(view, [replace_nth0/4]).

setup_kernel_call(M, Args, Index, ModuleHead, CallHead, Dict) :-
   variant_sha1(M, KernelId),
   maplist(get_dict(id), Args, Ids),
   append(Ids, Index, IdsIndex),
   Head =.. [KernelId, M.id | IdsIndex],
   ModuleHead = kernel:Head,

   maplist(get_dict(data), Args, Datas),
   append(Datas, Index, DatasIndex),
   CallHead =.. [KernelId, M.data | DatasIndex],
   Dict = M.put([kernel=(kernel:CallHead), index=Index]).

compile_expr(Op, Args, Index, Value, AST) :-
   % index inputs
   maplist(array:index_input(Index), Args, Pairs),
   pairs_keys_values(Pairs, ASTs, Values),
   foldl(mkconj, ASTs, true, BaseAST),

   % inline elementwise op using op_expr
   pairs_keys_values(PairsForRbtree, Args, Values),
   ord_list_to_rbtree(PairsForRbtree, ArgTree),
   phrase(op_expr(Op, Expr, ArgTree), []),

   % evaluate the expression, handling comparisons
   (  Expr =.. [<|_]
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
array:M.compile(prolog, contiguous(Parent)) := Dict :-
   Dict = M.compile(prolog, elementwise(contiguous(Parent))).
array:M.compile(prolog, A<B) := Dict :-
   Dict = M.compile(prolog, elementwise(A<B)).
array:M.compile(prolog, A+B) := Dict :-
   Dict = M.compile(prolog, elementwise(A+B)).
array:M.compile(prolog, A*B) := Dict :-
   Dict = M.compile(prolog, elementwise(A*B)).
array:M.compile(prolog, elementwise(Op)) := Dict :-
   length(Index, M.ndim()),
   phrase(op_args(Op), AllArgs),
   list_to_ord_set(AllArgs, Args),
   setup_kernel_call(M, Args, Index, ModuleHead, CallHead, Dict),

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
   phrase(op_args(Parent), AllArgs),
   list_to_ord_set(AllArgs, Args),
   setup_kernel_call(M, Args, Index, ModuleHead, CallHead, Dict),

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

op_args(Array), is_dict(Array, array) ==>
   [Array].
op_args(Op) ==>
   { Op =.. [_ | Args] },
   sequence(op_args, Args).

op_expr(A, R, Index), is_dict(A, array) ==>
   { rb_lookup(A, R, Index) }.
op_expr(contiguous(A), R, Index) ==>
   op_expr(A, R, Index).
op_expr(A+B, R, Index) ==>
   op_expr(A, A1, Index),
   op_expr(B, B1, Index),
   { R = (A1+B1) }.
op_expr(A*B, R, Index) ==>
   op_expr(A, A1, Index),
   op_expr(B, B1, Index),
   { R = (A1*B1) }.
op_expr(A<B, R, Index) ==>
   op_expr(A, A1, Index),
   op_expr(B, B1, Index),
   { R = (A1<B1) }.
