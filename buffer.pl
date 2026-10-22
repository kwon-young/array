:- module(buffer, [
   buffer_alloc/4,
   buffer_offset/5,
   buffer_from_data/4,
   buffer_from_data/5,
   buffer_to_data/4,
   buffer_to_data/5,
   buffer_type_size/2
]).

% The foreign libraries are built in build/, by a step before starting
% Prolog: see CMakeLists.txt.
:- multifile user:file_search_path/2.
:- dynamic user:file_search_path/2.

foreign_directory(Dir), user:file_search_path(foreign, Dir) =>
   true.
foreign_directory(Dir) =>
   asserta(user:file_search_path(foreign, Dir)).

:- prolog_load_context(directory, Dir),
   directory_file_path(Dir, build, Build),
   foreign_directory(Build).

:- use_foreign_library(foreign(buffer)).

buffer_type_size(Type, TypeSize) :-
   c_buffer_type_size(Type, TypeSize).

buffer_alloc(Buffer, Type, Size, Zero) :-
   c_buffer_type_size(Type, TypeSize),
   BufferSize is Size*TypeSize,
   c_buffer_alloc(Buffer, BufferSize, Zero).

buffer_offset(Buffer, Type, Size, Offset, Pointer) :-
   Offset =< Size,
   c_buffer_type_size(Type, TypeSize),
   PointerOffset is Offset * TypeSize,
   c_buffer_pointer(Buffer, PointerOffset, Pointer).

buffer_from_data(Buffer, Type, Size, Data) :-
   buffer_from_data(Buffer, Type, 0, Size, Data).

% Buffer is a new buffer holding the Size arguments of Data from Offset.
buffer_from_data(Buffer, Type, Offset, Size, Data) :-
   buffer_alloc(Buffer, Type, Size, false),
   c_buffer_from_compound(Buffer, Type, Offset, Size, Data).

buffer_to_data(Buffer, Type, Size, Data) :-
   buffer_to_data(Buffer, Type, 0, Size, Data).

% Data holds the Size elements of Buffer from Offset.
buffer_to_data(Buffer, Type, Offset, Size, Data) :-
   c_buffer_to_compound(Buffer, Type, Offset, Size, data, Data).
