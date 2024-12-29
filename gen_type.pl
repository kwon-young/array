:- module(gen_type, [main/0, type/3, pl_c_type/2]).

:- use_module(library(dcg/basics)).
:- use_module(library(dcg/high_order)).
:- use_module(c99).

type(bool, '_Bool', bool).
type(int8, int8_t, int64).
type(int16, int16_t, int64).
type(int32, int32_t, int64).
type(int64, int64_t, int64).
type(uint8, uint8_t, uint64).
type(uint16, uint16_t, uint64).
type(uint32, uint32_t, uint64).
type(uint64, uint64_t, uint64).
type(float16, '_Float16', float).
type(float32, '_Float32', float).
type(float64, '_Float64', float).

pl_c_type(int64, int64_t).
pl_c_type(uint64, uint64_t).
pl_c_type(float, double).
pl_c_type(bool, int).

include -->
   [  #(include(<>, 'SWI-Prolog.h')),
      #(include(<>, 'stdint.h'))
   ].

type_atom(Type, Name) :-
   atomic_list_concat(['ATOM_', Type], Name).

declare -->
   foreach(type(Type, _, _), declare(Type)).

declare(Type) -->
   {type_atom(Type, Name)},
   ['static atom_t':Name].

load -->
   {findall(AST, load(AST), ASTs), comma_list(List, ASTs)},
   [  'static int':load('void*':buffer, size_t:size, atom_t:type, size_t:offset, term_t:v) {
         List,
         return('FALSE')
      }
   ].

if_type(Type, Body, AST) :-
   type(Type, CType, _),
   type_atom(Type, Atom),
   AST = (
      if(type == Atom && (offset+1)*sizeof(CType) =< size) {
         Body
      }
   ).

load(AST) :-
   type(Type, CType, PlType),
   atomic_list_concat(['PL_unify_', PlType], Unify),
   Return =.. [Unify, v, *(cast(buffer, *CType) + offset)],
   if_type(Type, return(Return), AST).

set -->
   {findall(AST, set(AST), ASTs), comma_list(List, ASTs)},
   ['static int':set('void*':buffer, size_t:size, atom_t:type, size_t:offset, term_t:v_t) {
      List,
      return('FALSE')
   }
   ].

set(AST) :-
   type(Type, CType, PlType),
   pl_c_type(PlType, PlCType),
   atomic_list_concat(['PL_get_', PlType, '_ex'], Get),
   GetCall =.. [Get, v_t, &v],
   Body = (
      PlCType:v,
      GetCall,
      *(cast(buffer, *CType) + offset) = v,
      return('TRUE')
   ),
   if_type(Type, Body, AST).

atom_size -->
   {findall(AST, atom_size(AST), ASTs), comma_list(List, ASTs)},
   ['static int':atom_size(atom_t:type, 'size_t*':size) {
      List,
      return('FALSE')
   }].

atom_size(AST) :-
   type(Type, CType, _),
   type_atom(Type, Atom),
   AST = (
      if(type == Atom) {
         *size = sizeof(CType),
         return('TRUE')
      }
   ).

install -->
   {findall(AST, install(AST), ASTs), comma_list(List, ASTs)},
   ['static void':install_types(void) {
      List
   }].

install(Atom = 'PL_new_atom'(String)) :-
   type(Type, _, _),
   type_atom(Type, Atom),
   atom_string(Type, String).

main :-
   phrase((
      include,
      declare,
      load, set, atom_size, install), AST),
   phrase(translation_unit(AST), Tokens),
   phrase(tokens(Tokens), L),
   open("buffer_types.h", write, Stream),
   format(Stream, "~s", [L]),
   close(Stream).
