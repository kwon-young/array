:- module(linalg, [matmul/6, dot/4, cholesky/3, blocked_cholesky/4, batched_cholesky/4, spd/2]).
:- use_module(library(array)).

% Linear algebra as boxes: products, and Cholesky factorizations, plain, blocked and batched.

matmul(A, B, C, N, M, P) :-
   shape(A, [N, M]), shape(B, [M, P]), shape(C, [N, P]),
   over([I:N, J:P], [C[I, J] := 0]),
   over([I:N, J:P, K:M], [C[I, J] := C[I, J] + A[I, K] * B[K, J]]).

dot(A, B, S, N) :-
   shape(A, [N]), shape(B, [N]), shape(S, []),
   over([], [S := 0]),
   over([K:N], [S := S + A[K] * B[K]]).

% cholesky(+A, -L, +N): L lower triangular with L L^T = A, right-looking: per column K, the
% column scaled into C, stored, and the trailing triangle updated by C's outer product.
cholesky(A, L, N) :-
   shape(A, [N, N]), shape(L, [N, N]), shape(C, [N]),
   over([I:N, J:N], [L[I, J] := where(J =< I, A[I, J], 0)]),
   over([K:N], [over([I:N], [C[I] := where(I =:= K, sqrt(L[K, K]), where(K < I, L[I, K] / sqrt(L[K, K]), 0))]),
                over([I:N], [L[I, K] := where(K =< I, C[I], L[I, K])]),
                over([I:N, J:N], [L[I, J] := where(K < J, where(J =< I, L[I, J] - C[I] * C[J], L[I, J]), L[I, J])])]).

% spd(+N, -Vals): the matrix min(i, j) + 1, whose Cholesky factor is the triangle of ones.
spd(N, Vals) :-
   findall(V, ( between(0, N, I), I < N, between(0, N, J), J < N, V is min(I, J) + 1 ), Vals).

% blocked_cholesky(+A, -L, +N, +NB): L L^T = A by panels of NB columns. Per panel: a sweep
% factors the diagonal block; the panel's columns are copied to P, from which a kernel per
% row solves the rows below the block against the block, L21 = A21 L11^-T; the finished panel
% is copied to P again, and the trailing matrix loses its outer product, a staged reduction
% over the panel's columns launched over the active block only.
blocked_cholesky(A, L, N, NB) :-
   Panels is N // NB,
   shape(A, [N, N]), shape(L, [N, N]), shape(C, [N]), shape(P, [N, NB]), shape(S, []),
   over([I:N, J:N], [L[I, J] := where(J =< I, A[I, J], 0)]),
   over([Kb:Panels], [
      over([K:NB], [over([I:N], [C[I] := where(I =:= Kb*NB + K, sqrt(L[Kb*NB + K, Kb*NB + K]),
                                         where(Kb*NB + K < I, where(I < Kb*NB + NB,
                                               L[I, Kb*NB + K] / sqrt(L[Kb*NB + K, Kb*NB + K]), 0), 0))]),
                    over([I:N], [L[I, Kb*NB + K] := where(Kb*NB + K =< I, where(I < Kb*NB + NB, C[I], L[I, Kb*NB + K]),
                                                           L[I, Kb*NB + K])]),
                    over([I:N, J:N], [L[I, J] := where(Kb*NB + K < J, where(J < Kb*NB + NB, where(J =< I, where(I < Kb*NB + NB,
                                                 L[I, J] - C[I] * C[J], L[I, J]), L[I, J]), L[I, J]), L[I, J])])]),
      over([I:N, Kk:NB], [P[I, Kk] := L[I, Kb*NB + Kk]]),
      over([I:N], [over([J:NB], [over([], [S := 0]),
                                 over([Kk:NB], [S := S + where(Kk < J, L[I, Kb*NB + Kk] * P[Kb*NB + J, Kk], 0)]),
                                 L[I, Kb*NB + J] := where(Kb*NB + NB =< I, (L[I, Kb*NB + J] - S) / P[Kb*NB + J, J],
                                                          L[I, Kb*NB + J])])]),
      over([I:N, Kk:NB], [P[I, Kk] := L[I, Kb*NB + Kk]]),
      over([I:N, J:N, Kk:NB], [L[I, J] := where(Kb*NB + NB =< J, where(J =< I, L[I, J] - P[I, Kk] * P[J, Kk], L[I, J]), L[I, J])])]).

batched_cholesky(A, L, M, N) :-
   shape(A, [M, N, N]), shape(L, [M, N, N]), shape(C, [M, N]),
   over([B:M, I:N, J:N], [L[B, I, J] := where(J =< I, A[B, I, J], 0)]),
   over([B:M, K:N], [over([I:N], [C[B, I] := where(I =:= K, sqrt(L[B, K, K]), where(K < I, L[B, I, K] / sqrt(L[B, K, K]), 0))]),
                     over([I:N], [L[B, I, K] := where(K =< I, C[B, I], L[B, I, K])]),
                     over([I:N, J:N], [L[B, I, J] := where(K < J, where(J =< I, L[B, I, J] - C[B, I] * C[B, J], L[B, I, J]), L[B, I, J])])]).
