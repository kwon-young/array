:- module(c99, [
   translation_unit//1, tokens//1,
   op(200, yf, ++),
   op(200, yf, --),
   op(700, xfx, +=),
   op(700, xfx, -=),
   op(200, fy, *),
   op(200, fy, &),
   op(60, yf, {}),
   op(20, yf, []),
   op(40, xfy, else),
   op(40, fy, if),
   op(1000, xfy, &&)
]).

:- use_module(library(dcg/basics)).
:- use_module(library(dcg/high_order)).

translation_unit(TL) -->
   {  (  is_list(TL)
      -> TL = List
      ;  comma_list(TL, List)
      )
   },
   sequence(external_decl, List).

pp(#(Exp)) -->
   [#], include(Exp), [eol()].

include(include(Name)) -->
   [include], litteral(Name).
include(include(<>, Name)) -->
   {atomic_list_concat([<, Name, >], Include)},
   [include, atom(Include)].

external_decl(Decl) -->
   (  pp(Decl)
   ;  function(Decl)
   ;  prototype(Decl), [;]
   ;  decl(Decl), [;]
   ).

function(ReturnType:NameParams {Body}) -->
   type(ReturnType), exp(NameParams),
   compound_statement(Body).
function((ReturnType:NameParams) {Body}) -->
   type(ReturnType), exp(NameParams),
   compound_statement(Body).

params(Params) -->
   ['('], sequence(exp, [','], Params), [')'].

type(Type) -->
   {must_be(nonvar, Type)},
   {atom(Type)}, [atom(Type)].
type(*Type) -->
   type(Type), [*].

decl(Type:Name) -->
   type(Type), exp(Name).

prototype(prototype(Type, Name, Params)) -->
   type(Type), name(Name), params(Params).

name(Name) -->
   {atom(Name)}, [atom(Name)].

compound_statement(Statements) -->
   { comma_list(Statements, List) },
   ['{'], sequence(statement, List), ['}'].

statement(Decl) -->
   decl(Decl), [;].
statement({}(Statement)) -->
   compound_statement(Statement).
statement(for(Init, Cond, End) {Body}) -->
   [for, '('], exp(Init), [;], exp(Cond), [;], exp(End), [')'],
   compound_statement(Body).
statement(while(Cond) {Body}) -->
   [while, '('], exp(Cond), [')'], compound_statement(Body).
statement(if A else B) -->
   statement(if A),
   [else], statement(B).
statement(if Cond { Then }) -->
   [if, '('], exp(Cond), [')'],
      compound_statement(Then).
statement(return(X)) -->
   [return], exp(X), [;].
statement(;) -->
   [].
statement(Exp) -->
   exp(Exp), [;].

exp(Litteral) -->
   litteral(Litteral).
exp(Name) -->
   name(Name).
exp(Name) -->
   decl(Name).
exp(cast(A, Type)) -->
   ['('], type(Type), [')', '('], exp(A), [')'].
exp(A = B) -->
   exp(A), [=], exp(B).
exp(A += B) -->
   exp(A), [+=], exp(B).
exp(A -= B) -->
   exp(A), [-=], exp(B).
exp(A == B) -->
   exp(A), [==], exp(B).
exp(A =< B) -->
   exp(A), ['<='], exp(B).
exp(A < B) -->
   exp(A), [<], exp(B).
exp(A > B) -->
   exp(A), [>], exp(B).
exp(A + B) -->
   ['('], exp(A), [+], exp(B), [')'].
exp(A - B) -->
   ['('], exp(A), [-], exp(B), [')'].
exp(A * B) -->
   exp(A), [*], exp(B).
exp(A / B) -->
   exp(A), [/], exp(B).
exp(A && B) -->
   exp(A), [&&], exp(B).
exp(Exp[Size]) -->
   exp(Exp), ['[', integer(Size), ']'].
exp(*Exp) -->
   [*, '('], exp(Exp), [')'].
exp(&Exp) -->
   [&], exp(Exp).
exp(Exp++) -->
   exp(Exp), [++].
exp(dot(A, B)) -->
   exp(A), ['.'], exp(B).
exp(Compound) -->
   {compound(Compound), compound_name_arguments(Compound, Name, Args)},
   name(Name), params(Args).

litteral(Integer) -->
   {integer(Integer)}, [integer(Integer)].
litteral(Float) -->
   {float(Float)}, [float(Float)].
litteral(String) -->
   {string(String), atomic_list_concat(['"', String, '"'], Atom)},
   [atom(Atom)].

token(Token) -->
   (  {atom(Token)}
   -> atom(Token)
   ;  call(Token)
   ).

tokens(Tokens) -->
   sequence(token, " ", Tokens).
