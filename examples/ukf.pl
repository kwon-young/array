:- module(ukf, [ukf_step/5, ukf_order/6, chol/4, cv_range_model/3]).
:- use_module(library(array)).
:- use_module(sort).
:- use_module(library(clpBNR)).

/** <module> One step of an unscented Kalman filter, as boxes

The step of pclp_ukf.pl on a batch of B states of dimension N, scored against D detections
of dimension M. The prior of state b is its mean Mu[b] and covariance P[b]; the 2N sigma
points are Mu +- the columns of chol(N P), with equal weights 1/2N. The model is a predicate
Model(Xs, Ys, Zs): given the N reads of one sigma point it gives N value expressions, the
transformed state, and M, the predicted observation; one box runs it at every sigma point
of every state. The moments of the transformed points give the prediction, the innovation
covariance Szz = cov(Z) + R is inverted through its Cholesky factor, and every state is
scored against every detection: the negative log-likelihood of the detection under the
predicted observation, inf outside the gate D2 =< Crit. The Kalman update follows for every
state and detection pair, the mean per pair and the covariance per state, since it does not
depend on the detection taken; MuSel is the posterior mean of the detection Sel[b] chosen
for each state. N and M are the model's, ground; B and D may stay extent variables.

    ukf_step(+Model, +dims(B, N, M, D), +Crit, +in(Mu, P, R, Zdet, Sel), -Out)
        Mu[B, N], P[B, N, N], R[M, M], Zdet[D, M], Sel[B] in 0..D-1, ints
        Out = out(MuPred, PPred, MuZ, Szz, Score, MuPost, PPost, MuSel)
        MuPred[B, N], PPred[B, N, N], MuZ[B, M], Szz[B, M, M], Score[B, D],
        MuPost[B, D, N], PPost[B, N, N], MuSel[B, N]

    ukf_order(+Score, +dims(B, D), +Keys, +Vals, +Ks, +Ss)
        the state and detection pairs by ascending score: Vals[N] the pair indices b*D + d
        and Keys[N] their scores, in that order, the pairs beyond the gate last by their
        infinite score, after them -1 under inf for the padding. Keys and Vals are names of
        N elements given to the run and overwritten, N a power of two at least B*D; Ks and
        Ss the pass table of N, see sorting:pass_table/3.
*/

ukf_step(Model, dims(B, N, M, D), Crit, in(Mu, P, R, Zdet, Sel),
         out(MuPred, PPred, MuZ, Szz, Score, MuPost, PPost, MuSel)) :-
   K is 2*N, Nf is float(N), W is 1/float(K), C0 is 0.5*M*log(2*pi), Inf is inf,
   shape(Mu, [B, N]), shape(P, [B, N, N]), shape(R, [M, M]), shape(Zdet, [D, M]),
   shape(Sel, [B]), elements(Sel, 0-(D-1)),
   % Sigma points: X[b, s*N + j] = Mu[b] + (1 - 2 s) L[b][:, j], L L^T = N P.
   shape(S, [B, N, N]), shape(X, [B, K, N]),
   over([Bi:B, I:N, J:N], [S[Bi, I, J] := Nf * P[Bi, I, J]]),
   chol(S, L, B, N),
   over([Bi:B, Sg:2, J:N, I:N], [X[Bi, Sg*N + J, I] := Mu[Bi, I] + (1.0 - 2.0*Sg) * L[Bi, I, J]]),
   % The model at every sigma point of every state.
   shape(Y, [B, K, N]), shape(Z, [B, K, M]),
   Nm1 is N-1, Mm1 is M-1, numlist(0, Nm1, Is), numlist(0, Mm1, Js),
   maplist(read_of(X, Bi, Ki), Is, Xs),
   call(Model, Xs, Ys, Zs),
   maplist(write_of(Y, Bi, Ki), Is, Ys, EqY),
   maplist(write_of(Z, Bi, Ki), Js, Zs, EqZ),
   append(EqY, EqZ, Eqs),
   over([Bi:B, Ki:K], Eqs),
   % Moments of the transformed points.
   shape(MuPred, [B, N]), shape(MuZ, [B, M]),
   shape(PPred, [B, N, N]), shape(Szz, [B, M, M]), shape(Pyz, [B, N, M]),
   over([Bi:B, I:N], [MuPred[Bi, I] := 0]),
   over([Bi:B, I:N, Ki:K], [MuPred[Bi, I] := MuPred[Bi, I] + Y[Bi, Ki, I] * W]),
   over([Bi:B, I:M], [MuZ[Bi, I] := 0]),
   over([Bi:B, I:M, Ki:K], [MuZ[Bi, I] := MuZ[Bi, I] + Z[Bi, Ki, I] * W]),
   over([Bi:B, I:N, J:N], [PPred[Bi, I, J] := 0]),
   over([Bi:B, I:N, J:N, Ki:K],
        [PPred[Bi, I, J] := PPred[Bi, I, J] + (Y[Bi, Ki, I] - MuPred[Bi, I]) * (Y[Bi, Ki, J] - MuPred[Bi, J]) * W]),
   over([Bi:B, I:M, J:M], [Szz[Bi, I, J] := R[I, J]]),
   over([Bi:B, I:M, J:M, Ki:K],
        [Szz[Bi, I, J] := Szz[Bi, I, J] + (Z[Bi, Ki, I] - MuZ[Bi, I]) * (Z[Bi, Ki, J] - MuZ[Bi, J]) * W]),
   over([Bi:B, I:N, J:M], [Pyz[Bi, I, J] := 0]),
   over([Bi:B, I:N, J:M, Ki:K],
        [Pyz[Bi, I, J] := Pyz[Bi, I, J] + (Y[Bi, Ki, I] - MuPred[Bi, I]) * (Z[Bi, Ki, J] - MuZ[Bi, J]) * W]),
   % Szz^-1 = Linv^T Linv, Linv the inverse of the Cholesky factor by forward substitution,
   % a column per work item, its rows in order.
   chol(Szz, Ls, B, M),
   shape(Linv, [B, M, M]), shape(Acc, []), shape(Sinv, [B, M, M]),
   over([Bi:B, J:M], [over([I:M], [over([], [Acc := 0]),
                                   over([Kk:M], [Acc := Acc + where(Kk < I, Ls[Bi, I, Kk] * Linv[Bi, Kk, J], 0)]),
                                   Linv[Bi, I, J] := (where(I =:= J, 1.0, 0.0) - Acc) / Ls[Bi, I, I]])]),
   over([Bi:B, I:M, J:M], [Sinv[Bi, I, J] := 0]),
   over([Bi:B, I:M, J:M, Kk:M], [Sinv[Bi, I, J] := Sinv[Bi, I, J] + Linv[Bi, Kk, I] * Linv[Bi, Kk, J]]),
   % Every state against every detection: innovation, Mahalanobis distance, score.
   shape(E, [B, D, M]), shape(D2, [B, D]), shape(LogDet, [B]), shape(Score, [B, D]),
   over([Bi:B, Di:D, I:M], [E[Bi, Di, I] := Zdet[Di, I] - MuZ[Bi, I]]),
   over([Bi:B, Di:D], [D2[Bi, Di] := 0]),
   over([Bi:B, Di:D, I:M, J:M], [D2[Bi, Di] := D2[Bi, Di] + E[Bi, Di, I] * Sinv[Bi, I, J] * E[Bi, Di, J]]),
   over([Bi:B], [LogDet[Bi] := 0]),
   over([Bi:B, I:M], [LogDet[Bi] := LogDet[Bi] + 2.0 * log(Ls[Bi, I, I])]),
   over([Bi:B, Di:D], [Score[Bi, Di] := where(D2[Bi, Di] =< Crit, 0.5 * D2[Bi, Di] + 0.5 * LogDet[Bi] + C0, Inf)]),
   % The update: gain G = Pyz Szz^-1, a mean per pair, the covariance per state.
   shape(G, [B, N, M]), shape(GS, [B, N, M]),
   shape(MuPost, [B, D, N]), shape(PPost, [B, N, N]), shape(MuSel, [B, N]),
   over([Bi:B, I:N, J:M], [G[Bi, I, J] := 0]),
   over([Bi:B, I:N, J:M, Kk:M], [G[Bi, I, J] := G[Bi, I, J] + Pyz[Bi, I, Kk] * Sinv[Bi, Kk, J]]),
   over([Bi:B, Di:D, I:N], [MuPost[Bi, Di, I] := MuPred[Bi, I]]),
   over([Bi:B, Di:D, I:N, J:M], [MuPost[Bi, Di, I] := MuPost[Bi, Di, I] + G[Bi, I, J] * E[Bi, Di, J]]),
   over([Bi:B, I:N, J:M], [GS[Bi, I, J] := 0]),
   over([Bi:B, I:N, J:M, Kk:M], [GS[Bi, I, J] := GS[Bi, I, J] + G[Bi, I, Kk] * Szz[Bi, Kk, J]]),
   over([Bi:B, I:N, J:N], [PPost[Bi, I, J] := PPred[Bi, I, J]]),
   over([Bi:B, I:N, J:N, Kk:M], [PPost[Bi, I, J] := PPost[Bi, I, J] - GS[Bi, I, Kk] * G[Bi, J, Kk]]),
   over([Bi:B, I:N], [MuSel[Bi, I] := MuPost[Bi, Sel[Bi], I]]).

ukf_order(Score, dims(B, D), Keys, Vals, Ks, Ss) :-
   shape(Score, [B, D]), {B >= 1, D >= 1},
   shape(Keys, [N]), shape(Vals, [N]), kind(Keys, float), kind(Vals, int),
   Inf is inf,
   over([I:N], [Keys[I] := where(I < B*D, Score[min(I // D, B-1), I mod D], Inf),
                Vals[I] := where(I < B*D, I, -1)]),
   bitonic(Keys, Vals, Ks, Ss, N).

read_of(A, Bi, Ki, I, A[Bi, Ki, I]).
write_of(A, Bi, Ki, I, V, A[Bi, Ki, I] := V).

% chol(+A, -L, +B, +N): L[b] L[b]^T = A[b] for each of the B matrices, right-looking per
% column: the column scaled into C, stored, and the trailing triangle updated by its outer
% product.
chol(A, L, B, N) :-
   shape(A, [B, N, N]), shape(L, [B, N, N]), shape(C, [B, N]),
   over([Bi:B, I:N, J:N], [L[Bi, I, J] := where(J =< I, A[Bi, I, J], 0)]),
   over([Bi:B, K:N], [over([I:N], [C[Bi, I] := where(I =:= K, sqrt(L[Bi, K, K]), where(K < I, L[Bi, I, K] / sqrt(L[Bi, K, K]), 0))]),
                      over([I:N], [L[Bi, I, K] := where(K =< I, C[Bi, I], L[Bi, I, K])]),
                      over([I:N, J:N], [L[Bi, I, J] := where(K < J, where(J =< I, L[Bi, I, J] - C[Bi, I] * C[Bi, J], L[Bi, I, J]), L[Bi, I, J])])]).

% cv_range_model(+Xs, -Ys, -Zs): a constant-velocity track (x, y, vx, vy) over a half-unit
% step, observed as its range and its y.
cv_range_model([X, Y, Vx, Vy], [X + 0.5 * Vx, Y + 0.5 * Vy, Vx, Vy], [sqrt(X * X + Y * Y), Y]).
