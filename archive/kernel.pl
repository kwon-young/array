:- module(kernel, [compile/2]).

:- use_module(library(dcg/basics)).
:- use_module(library(dcg/high_order)).
:- use_module(library(clpfd)).
:- use_module(library(rbtrees)).

:- use_module(gen_type, [type/3, pl_c_type/2]).
:- use_module(swipl_ld).
:- use_module(c99).
:- use_module(array).
:- use_module(mem).
:- use_module(buffer).

identifiers(Base, N, Identifiers) :-
   numlist(1, N, Is),
   maplist({Base}/[I, Identifier]>>(atomic_list_concat([Base, I], Identifier)),
           Is, Identifiers).

get_dicts_same(Key, Dicts, Value) :-
   maplist({Key, Value}/[Dict]>>(get_dict(Key, Dict, Value)), Dicts).

param(Array, Param), Array.device = c =>
   is_dict(Array.buffer, buffer),
   type(Array.dtype, CType, _),
   Buffer = Array.name(),
   Param = CType:Buffer[Array.buffersize].

call_param(Array, Name), Array.device = c =>
   is_dict(Array.buffer, buffer),
   Name = Array.buffername().

convcomma(Goal, Arrays, Results) :-
   convlist(Goal, Arrays, List),
   comma_list(Results, List).
mapcomma(Goal, Args, Results) :-
   append(Args, [List], AllArgs),
   apply(maplist(Goal), AllArgs),
   comma_list(Results, List).

apply_offset(Array, Expr) :-
   (  Array.buffer = arange
   -> type(Array.dtype, CType, _),
      Expr = (CType:Array.name() = Array.offset)
   ;  Expr = (Array.name() += Array.offset)
   ).

iterate(Name, Output, (Prototype-Call)-AST) :-
   Arrays = [Output | Output.inputs()],
   convlist(param, Arrays, Params),
   mapcomma(apply_offset, [Arrays], AddOffsets),
   Function =.. [Name | Params],
   Prototype = (void:Function),
   convlist(call_param, Arrays, CallParams),
   Call =.. [Name | CallParams],
   AST = (
      #(include(<>, "stdint.h")),
      #(include(<>, "stddef.h")),
      #(include(<>, "time.h")),
      #(include(<>, "stdio.h")),
      Prototype {
         AddOffsets,
         Sub
      }
   ),
   get_dicts_same(shape, Arrays, Shape),
   maplist(get_dict(strides), Arrays, Strides),
   transpose(Strides, StridesT),
   identifiers(i, Output.ndim(), Indices),
   iterate(Shape, Indices, Arrays, StridesT, Sub).

access(Array, Access) :-
   (  Array.buffersize > 0
   -> Access = *Array.name()
   ;  Access = Array.name()
   ).

array_name(Array, Name) :-
   Name = Array.name().

name_expr(ExprIn, ExprOut), array:binary_op(ExprIn) =>
   ExprIn =.. [Op | ArgsIn],
   maplist(name_expr, ArgsIn, ArgsOut),
   ExprOut =.. [Op | ArgsOut].
name_expr(view(Array), Out) =>
   name_expr(Array, Out).
name_expr(Array, Name), is_dict(Array, array) =>
   access(Array, Name).

iterate([], [], [Output | _], [], Body) :-
   name_expr(Output.data, Expr),
   Body = (*Output.name() = Expr).
iterate([Dim | Shape], [I | Indices], Arrays, [DimStrides | Strides], Body) :-
   iterate(Shape, Indices, Arrays, Strides, Sub),
   mapcomma([Array, Stride, Name += Stride]>>array_name(Array, Name),
             [Arrays, DimStrides], AddStrides),
   mapcomma({Dim}/[Array, Stride, Name -= Dim*Stride]>>array_name(Array, Name),
            [Arrays, DimStrides], AddBackStrides),
   Body = (
      for(size_t:I = 0, I < Dim, I++) {
         Sub,
         AddStrides
      },
      AddBackStrides
   ).

empty(Name, Array, (Prototype-Call)-AST) :-
   Buffer = Array.name(),
   type(Array.dtype, CType, _),
   (  Array.data = empty(true)
   -> Size #= Array.buffersize * Array.itemsize(),
      Body = memset(cast(Buffer, 'void*'), 0, Size)
   ;  Body = (;)
   ),
   Function =.. [Name, CType:Buffer[Array.buffersize]],
   Prototype = (void:Function),
   Call =.. [Name, Array.buffername()],
   AST = (
      #(include(<>, "string.h")),
      #(include(<>, "stdint.h")),
      Prototype {
         Body
      }
   ).

from_list_kernel(Name, Array, AST) :-
   type(Array.dtype, CType, GetType),
   pl_c_type(GetType, PlType),
   atom_concat('PL_get_', GetType, Get),
   GetCall =.. [Get, head, &v],
   Buffer = Array.buffername(),
   Function =.. [Name, term_t:Array.termname(), CType:Buffer[Array.buffersize]],
   Prototype = (void:Function),
   AST = (
      #(include(<>, 'SWI-Prolog.h')),
      #(include(<>, "stdint.h")),
      Prototype {
         term_t:head = 'PL_new_term_ref'(),
         term_t:tail = 'PL_copy_term_ref'(Array.termname()),
         PlType:v;
         while('PL_get_list'(tail, head, tail)) {
            GetCall,
            *Buffer = v,
            Buffer++
         }
      }
   ).

kernel(Array, Prototype-Object) :-
   variant_sha1(Array, Id),
   atomic_list_concat([kernel_, Id], Name),
   (  Array.data = empty(_)
   -> empty(Name, Array, Prototype-AST)
   ;  Array.data = from_list(_)
   -> from_list_kernel(Name, Array, Prototype-AST)
   ;  iterate(Name, Array, Prototype-AST)
   ),
   once((
      phrase(translation_unit(AST), Tokens),
      phrase(tokens(Tokens), Codes)
   )),
   clang_format(Codes, Formatted),
   compile_object(Formatted, Object).

fuse(ArraysIn, ArraysOut), select(ArrayIn, ArraysIn, ArrayOut, ArraysTmp),
                           fuse_(ArrayIn, ArrayOut) =>
   fuse(ArraysTmp, ArraysOut).
fuse(ArraysIn, ArraysOut) =>
   ArraysOut = ArraysIn.

fuse_(ArrayIn, ArrayOut), is_dict(ArrayIn, array),
                          fuse(ArrayIn, ArrayIn.data, DataOut) =>
   ArrayOut = ArrayIn.put([data=DataOut]).
fuse_(ArrayIn, ArrayOut), is_dict(ArrayIn, array),
                          fuse_(ArrayIn.data, DataOut) =>
   ArrayOut = ArrayIn.put([data=DataOut]).
fuse_(In, Out), \+ is_dict(In, array),
                In =.. [F | ArgsIn],
                select(ArgIn, ArgsIn, ArgOut, ArgsOut),
                fuse_(ArgIn, ArgOut) =>
   Out =.. [F | ArgsOut].
fuse_(_, _) => fail.

fuse(Array, Data, Out) :-
   array:binary_op(Data),
   Data =.. [Op | ArgsIn],
   once((
      select(ArgIn, ArgsIn, ArgOut, ArgsOut),
      fuse_(Array, ArgIn, ArgOut)
   )),
   Out =.. [Op | ArgsOut].

fuse_(Parent, Child, Out), is_dict(Child, array),
                           fusable(Parent, Child, Child.data) =>
   Out = Child.data.
fuse_(Parent, view(Sub), Out) =>
   fuse_(Parent, Sub, Out).
fuse_(Parent, Data, Out), array:binary_op(Data) =>
   fuse(Parent, Data, Out).
fuse_(_, _, _) => fail.

fusable(Parent, Child, Data), array:binary_op(Data) =>
   compound_name_arguments(Data, _, Args),
   maplist(fusable(Parent, Child), Args).
fusable(Parent, Child, view(Sub)) =>
   fusable(Parent, Child, Sub).
fusable(Parent, Child, Data), is_dict(Data, array) =>
   get_dicts_same(shape, [Parent, Child, Data], _SameShape).
fusable(_, _, _) => fail.

compile(c, Arrays) :-
   fuse(Arrays, FusedArrays),
   once(allocation_plan(FusedArrays, Inputs, AllNodes, Buffers, MaxAllocationSize)),
   exclude([Array]>>(
      get_dict(data, Array, Data),
      (  Data = view(_)
      -> true
      ;  Data = arange
      -> true
      )), AllNodes, Nodes),
   maplist(kernel, Nodes, KernelObjects),
   variant_sha1(FusedArrays, Id),
   atom_concat(graph_, Id, GraphName),
   compile_c_graph(GraphName, Inputs, FusedArrays, Buffers, MaxAllocationSize, KernelObjects).

array_input_param(Array, Array.input(), term_t:Array.termname()).

buffer_pointer(Buffer, 'void*':Buffer.name() = buffer+Buffer.pstart).

compile_c_graph(GraphName, Inputs, Outputs, Buffers, MaxAllocationSize, KernelsObjects) :-
   maplist(array_input_param, Inputs, InputTerms, InputArgs),
   Function =.. [GraphName, term_t:buffer_t | InputArgs],
   pairs_keys_values(KernelsObjects, PrototypesCalls, Objects),
   pairs_keys_values(PrototypesCalls, PrototypesList, CallList),
   comma_list(Prototypes, PrototypesList),
   maplist(buffer_pointer, Buffers, PointerList),
   comma_list(Pointers, PointerList),
   comma_list(Calls, CallList),
   atom_string(GraphName, GraphNameStr),
   length(Inputs, NumInput),
   Arity #= NumInput + 1,
   AST = (
      #(include(<>, "stdint.h")),
      #(include(<>, "stddef.h")),
      #(include(<>, "SWI-Prolog.h")),
      #(include(<>, "time.h")),
      #(include(<>, "stdio.h")),
      Prototypes,
      'static foreign_t':Function {
         'struct timespec':tms,
         int64_t:micros,
         'void*':buffer,
         if(!('PL_get_blob'(buffer_t, &buffer, 'NULL', 'NULL'))) {
            return('FALSE')
         },
         Pointers,
         Calls,
         return('TRUE')
      },
      install_t:install() {
         'PL_register_foreign'(GraphNameStr, Arity, GraphName, 0)
      }
   ),
   once((
      phrase(translation_unit(AST), Tokens),
      phrase(tokens(Tokens), Codes)
   )),
   clang_format(Codes, Formatted),
   compile_object(Formatted, Object),
   link_objects([Object | Objects], Library),
   load_foreign_library(Library),
   alloc_buffer(Buffer, MaxAllocationSize, false),
   time(apply(GraphName, [Buffer | InputTerms])),
   maplist(buffer_output(Buffer), Outputs).

buffer_output(Buffer, Array) :-
   Offset = Array.buffer.pstart,
   Array.buffer.data = pointer(Buffer, Offset).
