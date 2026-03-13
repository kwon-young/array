:- module(buffer, [
   buffer_alloc/4,
   buffer_offset/5,
   buffer_from_data/4,
   buffer_to_data/4
]).

:- use_foreign_library('buffer.so').

buffer_alloc(Buffer, Type, Size, Zero) :-
   c_buffer_type_size(Type, TypeSize),
   BufferSize is Size*TypeSize,
   c_buffer_alloc(Buffer, BufferSize, Zero).

buffer_offset(Buffer, Type, Size, Offset, Pointer) :-
   Offset =< Size,
   c_buffer_type_size(Type, TypeSize),
   PointerOffset is Offset * TypeSize,
   c_buffer_pointer(Pointer, Buffer, PointerOffset).

buffer_from_data(Data, Type, Size, Buffer) :-
   buffer_alloc(Buffer, Type, Size, false),
   c_buffer_from_compound(Data, Buffer, Type, 0, Size).

buffer_to_data(Buffer, Type, Size, Data) :-
   c_buffer_to_compound(Data, Buffer, Type, 0, Size, data).
