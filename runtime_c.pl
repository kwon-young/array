:- module(runtime_c, []).

:- use_module(array, []).
:- use_module(buffer).
:- use_module(c99).
:- use_module(swipl_ld).
:- use_module(gen_type).
:- use_module(dtype).
:- use_module(precision, [transfer_precision/3]).
:- use_module(kernel_c).

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
   compile_kernel(M, cast(rand(), M.dtype()) / 'RAND_MAX', Dict).
array:M.compile(c, float(A)) := Dict :-
   compile_kernel(M, cast(A, M.dtype()), Dict).
array:M.compile(c, integer(A)) := Dict :-
   integer_cast(A, M.dtype(), Expr),
   compile_kernel(M, Expr, Dict).
array:M.compile(c, Op) := Dict :-
   compile_kernel(M, Op, Dict).

% compile_kernel(+M, +Expr, -Dict)
% Dict is M with a kernel storing the value of Expr at each index of M.
compile_kernel(M, Expr, Dict) :-
   kernel_params(M, Expr, Args, Index, Params),
   kernel_body(c, M, Expr, Args, Index, Body),
   length(Args, NArgs),
   opt_level(Level),
   Code = code(Level, Params, M.shape(), Body),
   % A kernel is named after its code, so a kernel already loaded is reused.
   variant_sha1(Code, Hash),
   atom_concat(kernel_, Hash, KernelName),
   atom_concat(runtime_, Hash, RuntimeName),
   kernel_ast(KernelName, RuntimeName, Code, AST),
   name_variables(AST),
   N is 1 + NArgs,
   load_kernel(RuntimeName/N, Level, AST),
   maplist(get_dict(data), Args, Buffers),
   Buffer = M.data,
   Kernel =.. [RuntimeName, Buffer | Buffers],
   Dict = M.put([kernel=runtime_c:Kernel]).

load_kernel(Runtime, _, _), current_predicate(Runtime) =>
   true.
load_kernel(_, Level, AST) =>
   once(phrase(translation_unit(AST), Tokens)),
   once(phrase(tokens(Tokens), Str)),
   clang_format(Str, In),
   debug(array(kernel), "~s", [In]),
   atom_concat('-O', Level, Optimize),
   % never -ffast-math: the precision bounds need IEEE rounding
   compile_object(In, [Optimize, '-march=native'], Object),
   link_objects([Object], Library),
   load_foreign_library(Library).

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

% kernel_params(+M, +Op, -Args, -Index, -Params)
% The kernel computing Op into M reads the buffers of Args at Index.
% Params are its typed parameters: a0 for M, a1... for Args, and Index.
kernel_params(M, Op, UniqueArgs, Index, params(Type:a0, TypeArgs, TypeIndex)) :-
   ids(M.ndim(), i, int, Index, TypeIndex),
   phrase(array:op_args(Op), AllArgs),
   list_to_ord_set(AllArgs, UniqueArgs),
   length(UniqueArgs, NArgs),
   maplist(array:dtype, UniqueArgs, PrologDTypes),
   maplist(type, PrologDTypes, DTypes, _, _),
   maplist([DType, P]>>atom_concat(DType, *, P), DTypes, Ps),
   type(M.dtype(), MDType, _, _),
   atom_concat(MDType, *, Type),
   ids(NArgs, a, Ps, _, TypeArgs).

% kernel_ast(+KernelName, +RuntimeName, +Code, -AST)
% AST defines the kernel, computing one index, and its runtime, a foreign
% predicate looping over every index.
kernel_ast(KernelName, RuntimeName,
           code(_Level, params(Out, TypeArgs, TypeIndex), Shape, Body),
           AST) :-
   append(TypeArgs, TypeIndex, TypeArgsIndex),
   Head =.. [KernelName, Out | TypeArgsIndex],
   maplist([_:Name, Name]>>true, TypeArgs, Args),
   maplist([_:I, I]>>true, TypeIndex, Index),
   append(Args, Index, ArgsIndex),
   Call =.. [KernelName, a0 | ArgsIndex],
   length(TypeArgs, NArgs),
   ids(NArgs, t, term_t, Terms, TypeTerms),
   RuntimeHead =.. [RuntimeName, term_t:t0 | TypeTerms],
   maplist(get_blob_data, Terms, TypeArgs, BlobAstList),
   (  BlobAstList == []
   -> BlobAsts = true
   ;  comma_list(BlobAsts, BlobAstList)
   ),
   get_blob_data(t0, Out, BlobAst),
   loops(Shape, TypeIndex, Call, LoopAst),
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
      Body
   },
   'static foreign_t':RuntimeHead {
      BlobAst,
      BlobAsts,
      LoopAst,
      return('TRUE')
   },
   install_t:install(void) {
      'PL_register_foreign'(RuntimeStr, N, RuntimeName, 0)
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
   % prolog floats hold every C value exactly
   Dict = M.empty(M1.shape(), [device(prolog), data(Data), precision(M1.precision)]).

array:M.to(prolog, c) := Dict :-
   M1 = M.contiguous().realize(),
   Copy = M.empty(M1.shape(), [device=c, data(Data)]),
   transfer_precision(M1, Copy, Dict),
   array:bind_default_format(Dict),
   buffer_from_data(Data, Dict.dtype(), M1.datasize, M1.data).
