:- module(point, [op(500, yfx, '.+'), op(100, yf,  ++)]).

% :- use_module(library(arithmetic), [arithmetic_function/1]).
% :- arithmetic_function('++'/1).

:- use_module(library(arithmetic_types), [arithmetic_function/1]).
:- arithmetic_function('.+'/2).

'++'(A, B) :-
   B is A + 1.

'.+'(A, B, C) :-
   C = point{x: X, y: Y},
   X is A.x + B.x,
   Y is A.y + B.y.
%
M.add_value(V) := R :-
   R = point{x: X, y: Y},
   X is M.x + V,
   Y is M.y + V.
M.add_point(P) := R :-
   R = point{x: X, y: Y},
   P1 is eval(P),
   X is M.x + P1.x,
   Y is M.y + P1.y.

main1(A) :-
   A is (1+1)++ .
main1(B) :-
   A = point{x: 1, y: 1},
   B is A.add_value(1+1).
main1(B) :-
   A = point{x: 1, y: 1},
   B is A.add_value((1+1)++).

main2(C) :-
   A = point{x: 1, y: 1},
   B = point{x: 2, y: 2},
   C is A .+ B.
main2(C) :-
   A = point{x: 1, y: 1},
   B = point{x: 2, y: 2},
   C is (A .+ B).add_value(3).
main2(C) :-
   A = point{x: 1, y: 1},
   B = point{x: 2, y: 2},
   C is A.add_point(A.+B).
main2(C) :-
   A = point{x: 1, y: 1},
   C is A.add_value(1+1).
main2(C) :-
   A = point{x: 1, y: 1},
   C is A.add_value(toto).
main2(C) :-
   C is point{x: 1, y: 1}.add_value(1+1).
