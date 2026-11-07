% plus(0, 0, 0).
% plus(s(0), 0, s(0)).
% plus( s(0), s(0), s(s(0)) ).

plus(0, B, B).
plus(s(A), B, s(Resultat)) :-
   plus(A, B, Resultat).
