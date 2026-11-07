:- use_module(library(array)).
:- ['../bench'].
:- use_module('../../examples/linalg').
:- use_module(library(array/opencl)).

% The plan of the blocked Cholesky, and the time of its parts: the panel sweep alone, the
% row solve alone, the trailing update alone, by programs with the other parts removed.

plan(Device, N, NB) :-
   blocked_cholesky(_, L, N, NB), compile:device(Device, Dev, _, _), device_options(Dev, Opts),
   kernels(L, Opts, Plan), forall(member(P, Plan), show(P, "")).

show(loop(_, E, Inner), Indent) :- format("~wloop ~w~n", [Indent, E]), string_concat(Indent, "  ", I1), forall(member(P, Inner), show(P, I1)).
show(K, Indent) :- get_dict(kind, K, groups), !, kernel{rows: R, phases: Ph, local: L} :< K, length(Ph, NP), format("~wgroups rows=~w phases=~w items=~w~n", [Indent, R, NP, L]).
show(K, Indent) :- kernel{par: Par, stage: St, local: Loc, ranges: Rg} :< K, functor(St, F, _), length(Rg, NR),
   format("~witems par=~w stage=~w locals=~w ranges=~w~n", [Indent, Par, F, Loc, NR]).

part(panel, A, L, N, NB) :-
   Panels is N // NB, shape(A, [N, N]), shape(L, [N, N]), shape(C, [N]),
   over([I:N, J:N], [L[I, J] := where(J =< I, A[I, J], 0)]),
   over([Kb:Panels], [
      over([K:NB], [over([I:N], [C[I] := where(I =:= Kb*NB + K, sqrt(L[Kb*NB + K, Kb*NB + K]),
                                         where(Kb*NB + K < I, where(I < Kb*NB + NB,
                                               L[I, Kb*NB + K] / sqrt(L[Kb*NB + K, Kb*NB + K]), 0), 0))]),
                    over([I:N], [L[I, Kb*NB + K] := where(Kb*NB + K =< I, where(I < Kb*NB + NB, C[I], L[I, Kb*NB + K]),
                                                           L[I, Kb*NB + K])]),
                    over([I:N, J:N], [L[I, J] := where(Kb*NB + K < J, where(J < Kb*NB + NB, where(J =< I, where(I < Kb*NB + NB,
                                                 L[I, J] - C[I] * C[J], L[I, J]), L[I, J]), L[I, J]), L[I, J])])]),
      over([I:N], [L[I, 0] := L[I, 0]])]).
part(solve, A, L, N, NB) :-
   Panels is N // NB, shape(A, [N, N]), shape(L, [N, N]), shape(P, [N, NB]), shape(S, []),
   over([I:N, J:N], [L[I, J] := where(J =< I, A[I, J], 0)]),
   over([Kb:Panels], [
      over([I:N, Kk:NB], [P[I, Kk] := L[I, Kb*NB + Kk]]),
      over([I:N], [over([J:NB], [over([], [S := 0]),
                                 over([Kk:NB], [S := S + where(Kk < J, L[I, Kb*NB + Kk] * P[Kb*NB + J, Kk], 0)]),
                                 L[I, Kb*NB + J] := where(Kb*NB + NB =< I, (L[I, Kb*NB + J] - S) / P[Kb*NB + J, J],
                                                          L[I, Kb*NB + J])])])]).
part(update, A, L, N, NB) :-
   Panels is N // NB, shape(A, [N, N]), shape(L, [N, N]), shape(P, [N, NB]),
   over([I:N, J:N], [L[I, J] := where(J =< I, A[I, J], 0)]),
   over([Kb:Panels], [
      over([I:N, Kk:NB], [P[I, Kk] := L[I, Kb*NB + Kk]]),
      over([I:N, J:N, Kk:NB], [L[I, J] := where(Kb*NB + NB =< J, where(J =< I, L[I, J] - P[I, Kk] * P[J, Kk], L[I, J]), L[I, J])])]).

probe(Device, N, NB) :-
   spd(N, As),
   forall(member(Part, [panel, solve, update]),
          ( part(Part, A, L, N, NB), format(atom(Lb), "~w ~d nb ~d", [Part, N, NB]),
            bench_data(Lb, L, [A-As], Device, [], 3) )).
