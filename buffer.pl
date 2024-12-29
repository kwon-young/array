:- module(buffer, [
   alloc_buffer/3,
   buffer_size/2,
   free_buffer/1,
   load_buffer/4,
   set_buffer/4,
   type_size/2,
   % from_list/3,
   to_list/5,
   pointer_buffer/3
]).

:- use_foreign_library('buffer.so').

M.id() := Id :-
   variant_sha1(M, Id).

M.name() := Name :-
   atom_concat(buffer_, M.id(), Name).
