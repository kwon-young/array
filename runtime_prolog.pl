:- module(runtime_prolog, []).

:- use_module(library(dcg/high_order)).
:- use_module(array, []).
:- use_module(view, [replace_nth0/4]).

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
   variant_sha1(M, KernelId),

   phrase(op_args(Op), AllArgs),
   list_to_ord_set(AllArgs, Args),

   % build predicate head
   length(Index, M.ndim()),
   maplist(get_dict(id), Args, Ids),
   append(Ids, Index, IdsIndex),
   Head =.. [KernelId, M.id | IdsIndex],
   ModuleHead = kernel:Head,

   % index inputs
   maplist(array:index_input(Index), Args, Pairs),
   pairs_keys_values(Pairs, ArgsAsts, ArgsValue),
   foldl(mkconj, ArgsAsts, true, ArgsAst),

   % index output
   MIndexExpr-MValidExpr = M.index_expr(Index),

   % arithmetic
   pairs_keys_values(PairsValues, Args, ArgsValue),
   ord_list_to_rbtree(ArgsValue, Index),
   mapsubterms(map_op(Index), Op, OpValue),
   (  Op == true
   -> ArgsValue = [MValue],
      MExpr = true
   ;  Expr =.. [Op | ArgsValue],
      (  Op = (<)
      -> MExpr = (Expr -> MValue = 1 ; MValue = 0)
      ;  MExpr = (MValue is Expr)
      )
   ),

   % Head :- Body
   mkconj(ArgsAst, MExpr, Body),
   Kernel = (ModuleHead :-
      Body,
      (  MValidExpr
      -> MIndex is MIndexExpr+1,
         nb_setarg(MIndex, M.id, MValue)
      ;  true
      )
   ),
   retractall(ModuleHead),
   asserta(Kernel),

   % callable head
   maplist(get_dict(data), Args, Datas),
   append(Datas, Index, DatasIndex),
   CallHead =.. [KernelId, M.data | DatasIndex],
   Dict = M.put([kernel=(kernel:CallHead), index=Index]).
array:M.compile(prolog, reduce(Op, Axes, Parent)) := Dict :-
   variant_sha1(M, KernelId),
   length(Index, M.ndim()),
   Head =.. [KernelId, M.id, Parent.id | Index],
   ModuleHead = kernel:Head,
   same_length(Axes, AccIndex),
   foldl(replace_nth0, AccIndex, Axes, Index, FullIndex),
   ParentAST-ParentValue = Parent.index_input(FullIndex),
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
   ParentShape = Parent.shape(),
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
   asserta(Kernel),
   CallHead =.. [KernelId, M.data, Parent.data | Index],
   Dict = M.put([kernel=(kernel:CallHead), index=Index]).

op_args(Array), is_dict(Array, array) ==>
   [Array].
op_args(Op) ==>
   { Op =.. [_ | Args] },
   sequence(op_args, Args).

op_expr(A+B, R, Index) ==>
   op_expr(A, A1, Index),
   op_expr(B, B1, Index),
   { rb_lookup(
   [R is A1+B1
