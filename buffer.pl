:- module(buffer, [
   alloc/4,
   offset/5,
   from_data/4
]).

:- use_foreign_library('buffer.so').

alloc(Buffer, Type, Size, Zero) :-
   cbuffer_type_size(Type, TypeSize),
   BufferSize is Size*TypeSize,
   cbuffer_alloc(Buffer, BufferSize, Zero).

offset(Buffer, Type, Size, Offset, Pointer) :-
   Offset =< Size,
   cbuffer_type_size(Type, TypeSize),
   PointerOffset is Offset * TypeSize,
   cbuffer_pointer(Pointer, Buffer, PointerOffset).

from_data(Data, Type, Size, Buffer) :-
   compound_name_arguments(Data, data, List),
   alloc(Buffer, Type, Size, false),
   cbuffer_from_list(List, Buffer, Type).

to_data(Buffer, Type, Size, Data) :-
   cbuffer_to_compound(Data, Buffer, Type, 0, Size, data).
