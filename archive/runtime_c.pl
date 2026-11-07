:- module(runtime_c, []).

:- use_module(array, []).
:- use_module(buffer).
:- use_module(c99).
:- use_module(swipl_ld).
:- use_module(gen_type).
:- use_module(dtype).
:- use_module(precision, [transfer_precision/3]).
:- use_module(kernel_c).
:- use_module(ir_lower, [lower_kernel/5]).
:- use_module(ir_optimize, [optimize_kernel/3]).
:- use_module(ir_index, []).
:- use_module(ir_c, [ir_c/3]).

% Floats default to float64; integers and booleans take the smallest dtype
% holding their range.
% The kernel IR's index arithmetic is simplified where the compiler can't.
ir_optimize:layers(c, Layers) :-
   Layers = [[ir_index:fd_int, ir_index:fd_between, ir_index:fd_add,
              ir_index:fd_mul, ir_index:fd_div, ir_index:fd_mod,
              ir_index:add_assoc, ir_index:add_comm, ir_index:div_split,
              ir_index:mod_split, ir_index:mod_small, ir_index:materialize]].

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
array:expression_op(c, _**_).
array:expression_op(c, where(_, _, _)).
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
array:M.compile(c, Op) := Dict :-
   compile_kernel(M, Op, Dict).

% compile_kernel(+M, +Op, -Dict)
% Dict is M with a kernel computing Op into M: the kernel IR of Op, printed
% as a C function computing one element, called by a runtime predicate
% looping over M's index.
compile_kernel(M, Op, Dict) :-
   lower_kernel(c, M, Op, IR0, Arrays),
   ir_kernel(IR0, RuntimeName),
   maplist(get_dict(data), Arrays, Datas),
   Kernel =.. [RuntimeName | Datas],
   Dict = M.put([kernel=runtime_c:Kernel]).

% ir_kernel(+IR0, -RuntimeName)
% RuntimeName names the foreign predicate running the IR clause IR0 on the
% buffers of its head.
ir_kernel(IR0, RuntimeName) :-
   optimize_kernel(c, IR0, IR),
   ir_c(c, IR, c_kernel(Buffers, Shape, TypeIndex, Body)),
   maplist(buffer_param, Buffers, [Out | TypeArgs]),
   length(TypeArgs, NArgs),
   opt_level(Level),
   Code = code(Level, params(Out, TypeArgs, TypeIndex), Shape, Body),
   % A kernel is named after its code, so a kernel already loaded is reused.
   variant_sha1(Code, Hash),
   atom_concat(kernel_, Hash, KernelName),
   atom_concat(runtime_, Hash, RuntimeName),
   kernel_ast(KernelName, RuntimeName, Code, AST),
   name_variables(AST),
   N is 1 + NArgs,
   load_kernel(RuntimeName/N, Level, AST).

% Runs the IR clause Kernel on Datas, its outputs unbound data(...) terms,
% through C buffers of the formats of its head.
array:run_ir(c, Kernel, Datas) :-
   ir_kernel(Kernel, RuntimeName),
   head_formats(Kernel, Formats),
   maplist(data_buffer, Datas, Formats, Buffers),
   Call =.. [RuntimeName | Buffers],
   call(runtime_c:Call),
   maplist(buffer_data, Datas, Formats, Buffers).

head_formats((Head :- _), Formats) :-
   Head =.. [_ | Pairs],
   pairs_values(Pairs, Formats).

% An input is copied into a buffer, an output gets a zeroed one.
data_buffer(Data, Format, Buffer), ground(Data) =>
   functor(Data, _, Size),
   buffer_from_data(Buffer, Format, Size, Data).
data_buffer(Data, Format, Buffer) =>
   functor(Data, _, Size),
   buffer_alloc(Buffer, Format, Size, true).

buffer_data(Data, _, _), ground(Data) =>
   true.
buffer_data(Data, Format, Buffer) =>
   functor(Data, _, Size),
   buffer_to_data(Buffer, Format, Size, Data).

% An output never overlaps an input: an input lives in the buffer pool until
% its reader has run.
buffer_param(Format-a0, Param) =>
   type_name(c, Format, Type),
   atom_concat(Type, ' *restrict', PointerType),
   Param = PointerType:a0.
buffer_param(Format-Name, Param) =>
   type_name(c, Format, Type),
   atomic_list_concat([const, ' ', Type, ' *restrict'], PointerType),
   Param = PointerType:Name.

load_kernel(Runtime, _, _), current_predicate(Runtime) =>
   true.
load_kernel(_, Level, AST) =>
   once(phrase(translation_unit(AST), Tokens)),
   once(phrase(tokens(Tokens), Str)),
   clang_format(Str, In),
   debug(array(kernel), "~s", [In]),
   atom_concat('-O', Level, Optimize),
   % never -ffast-math: the precision bounds need IEEE rounding
   % -fopenmp-simd only enables the simd pragmas: no threads
   compile_object(In, [Optimize, '-march=native', '-fno-math-errno',
                       '-fopenmp-simd'], Object),
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
   % varargs: a foreign predicate of fixed arity takes at most 10 arguments
   findall(t0+K, between(1, NArgs, K), Terms),
   RuntimeHead =.. [RuntimeName, term_t:t0, int:arity, 'void*':context],
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
   'static inline void':Head {
      Body
   },
   'static foreign_t':RuntimeHead {
      cast(arity, void),
      cast(context, void),
      BlobAst,
      BlobAsts,
      LoopAst,
      return('TRUE')
   },
   install_t:install(void) {
      'PL_register_foreign'(RuntimeStr, N, RuntimeName, 'PL_FA_VARARGS')
   }
   ).
% Allocates the physical memory or underlying data storage for Array on the 'c' device.
array:allocate(c, M) :-
    buffer_alloc(M.data, M.dtype(), M.datasize, true).

% Defines the type promotion rules on the 'c' device.
% array:broadcast_dtype(c, int64, int64).

array:M.to(c, prolog) := Dict :-
   M1 = M.contiguous().realize(),
   buffer_to_data(M1.data, M1.dtype(), M1.data_offset(), M1.size(), Data),
   % prolog floats hold every C value exactly
   Dict = M.empty(M1.shape(), [device(prolog), data(Data), precision(M1.precision)]).

array:M.to(prolog, c) := Dict :-
   M1 = M.contiguous().realize(),
   Copy = M.empty(M1.shape(), [device=c, data(Data)]),
   transfer_precision(M1, Copy, Dict),
   array:bind_default_format(Dict),
   buffer_from_data(Data, Dict.dtype(), M1.data_offset(), M1.size(), M1.data).
