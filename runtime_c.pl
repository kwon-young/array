:- module(runtime_c, []).

:- use_module(array, []).
:- use_module(buffer).
:- use_module(c99).
:- use_module(swipl_ld).
:- use_module(gen_type).
:- use_module(runtime_prolog, except([op_expr/3])).
:- use_module(view, [replace_nth0/4]).
:- use_module(dtype).
:- use_module(library(clpBNR), []).

array:M.dtype(c) := DType :-
   array:range_min_max(M.range, Min, Max),
   (  get_dict(precision, M, Precision)
   -> Options = [precision(Precision)]
   ;  Options = []
   ),
   once(dtype_info(DType, M.dtype, Min, Max, Options)).
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
   Dict = M.compile(c, elementwise(cast(rand(), Type) / 'RAND_MAX')).
array:M.compile(c, contiguous(Parent)) := Dict :-
   Dict = M.compile(c, elementwise(contiguous(Parent))).
array:M.compile(c, A<B) := Dict :-
   Dict = M.compile(c, elementwise(A<B)).
array:M.compile(c, A+B) := Dict :-
   Dict = M.compile(c, elementwise(A+B)).
array:M.compile(c, A*B) := Dict :-
   Dict = M.compile(c, elementwise(A*B)).
array:M.compile(c, sin(A)) := Dict :-
   Dict = M.compile(c, elementwise(sin(A))).
array:M.compile(c, log(A)) := Dict :-
   Dict = M.compile(c, elementwise(log(A))).
array:M.compile(c, sqrt(A)) := Dict :-
   Dict = M.compile(c, elementwise(sqrt(A))).
array:M.compile(c, float(A)) := Dict :-
   Dict = M.compile(c, elementwise(cast(A, M.dtype()))).
array:M.compile(c, integer(A)) := Dict :-
   Dict = M.compile(c, elementwise(cast(A, M.dtype()))).
array:M.compile(c, elementwise(Op)) := Dict :-
   compile_elementwise(Op, M, Dict).
array:M.compile(c, reduce(Op, Axes, Parent)) := Dict :-
   compile_reduce(Op, Axes, Parent, M, Dict).

compile_elementwise(Op, M, Dict) :-
   setup_kernel_call(M, Op, Args, Index, Head, RuntimeName-Runtime),
   compile_expr(M, Op, Args, Index, Body),
   MIndexExpr-MValidExpr = M.index_expr(Index),
   atom_string(RuntimeName, RuntimeStr),
   length(Args, NArgs),
   N is 1 + NArgs,
   AST = (
   #(include(<>, 'SWI-Prolog.h')),
   #(include(<>, 'stdint.h')),
   #(include(<>, 'stddef.h')),
   #(include(<>, 'stdbool.h')),
   #(include(<>, 'stdlib.h')),
   void:Head {
      if MValidExpr {
         Body,
         a0[MIndexExpr] = v0
      }
   },
   Runtime,
   install_t:install(void) {
      'PL_register_foreign'(RuntimeStr, N, RuntimeName, 0)
   }
   ),
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

compile_reduce(Op, Axes, Parent, M, Dict) :-
   setup_kernel_call(M, Parent, Args, Index, Head, RuntimeName-Runtime),
   length(Axes, NAxes),
   ids(NAxes, j, int, AccIndex, TypeAccIndex),
   foldl(replace_nth0, AccIndex, Axes, Index, FullIndex),
   compile_expr(M, Parent, Args, FullIndex, InnerBody),
   [Arg0|_] = Args,
   ParentShape = Arg0.shape(),
   maplist({ParentShape}/[Axis, Dim]>>nth0(Axis, ParentShape, Dim), Axes, Dims),
   Expr =.. [Op, acc, v0],
   (  Op == (<)
   -> AccExpr = if(Expr) { acc = v0 }
   ;  AccExpr = (acc = Expr)
   ),
   loops(Dims, TypeAccIndex, (InnerBody, AccExpr), InnerLoopAst),
   MIndexExpr-MValidExpr = M.index_expr(Index),
   atom_string(RuntimeName, RuntimeStr),
   length(Args, NArgs),
   N is 1 + NArgs,
   array:identity(Op, Identity),
   (  Identity == -inf
   -> c_identity(M.dtype(), Identity, CIdentity)
   ;  CIdentity = Identity
   ),
   type(M.dtype(), MDType, _, _),
   AST = (
   #(include(<>, 'SWI-Prolog.h')),
   #(include(<>, 'stdint.h')),
   #(include(<>, 'stddef.h')),
   #(include(<>, 'stdbool.h')),
   #(include(<>, 'math.h')),
   void:Head {
      if MValidExpr {
         MDType:acc = CIdentity,
         InnerLoopAst,
         a0[MIndexExpr] = acc
      }
   },
   Runtime,
   install_t:install(void) {
      'PL_register_foreign'(RuntimeStr, N, RuntimeName, 0)
   }
   ),
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
compile_expr(M, Op, Args, Index, AST) :-
   length(Args, NArgs),
   (  NArgs == 0
   -> Numbers = []
   ;  numlist(1, NArgs, Numbers)
   ),
   maplist(index_input(Index), Args, Numbers, ASTs, Values),
   foldl(mkconj, ASTs, true, BaseAST),

   pairs_keys_values(PairsForRbtree, Args, Values),
   ord_list_to_rbtree(PairsForRbtree, ArgTree),
   op_expr(Op, Expr, ArgTree),
   type(M.dtype(), DType, _, _),
   EvalAST = (DType:v0 = Expr),
   mkconj(BaseAST, EvalAST, AST).

op_expr(A, R, Index), is_dict(A, array) =>
   rb_lookup(A, R, Index).
op_expr(contiguous(A), R, Index) =>
   op_expr(A, R, Index).
op_expr('RAND_MAX', R, _Index) =>
   R = 'RAND_MAX'.
op_expr(rand(), R, _Index) =>
   R = rand().
op_expr(A+B, R, Index) =>
   op_expr(A, A1, Index),
   op_expr(B, B1, Index),
   R = (A1+B1).
op_expr(A*B, R, Index) =>
   op_expr(A, A1, Index),
   op_expr(B, B1, Index),
   R = (A1*B1).
op_expr(A/B, R, Index) =>
   op_expr(A, A1, Index),
   op_expr(B, B1, Index),
   R = (A1/B1).
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
op_expr(cast(A, Type), R, Index) =>
   op_expr(A, A1, Index),
   R = cast(A1, Type).

index_input(Index, Arg, ArgN, AST, V) :-
   IndexExpr-ValidExpr = Arg.index_expr(Index),
   (  array:skip_view(Arg.op, constant(Constant))
   -> IndexAST = (V = Constant)
   ;  IndexAST = (V = A[IndexExpr])
   ),
   atom_concat(a, ArgN, A),
   atom_concat(v, ArgN, V),
   type(Arg.dtype(), DType, _, _),
   AST = (
   DType:V = 0,
   if ValidExpr {
      IndexAST
   }
   ).

% Allocates the physical memory or underlying data storage for Array on the 'c' device.
array:allocate(c, M) :-
    buffer_alloc(M.data, M.dtype(), M.datasize, true).

% Defines the type promotion rules on the 'c' device.
% array:broadcast_dtype(c, int64, int64).

array:M.to(c, prolog) := Dict :-
   M1 = M.contiguous().realize(),
   buffer_to_data(M1.data, M1.dtype(), M1.datasize, Data),
   Dict = M.empty(M1.shape(), [device(prolog), data(Data)]).

array:M.to(prolog, c) := Dict :-
   M1 = M.contiguous().realize(),
   Dict = M.empty(M1.shape(), [device=c, data(Data)]),
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
