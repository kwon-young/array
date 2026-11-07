:- module(nn, [softmax/4, gelu/2, mlp/5, layer_norm/6, vit_block/6, scatter/5, embedding_backward/6]).
:- use_module(library(array)).

% Neural network layers as boxes: softmax, a transformer's MLP, layer norm and encoder block,
% and the scatters of a backward pass.

softmax(X, Y, R, D) :-
   shape(X, [R, D]), shape(Y, [R, D]),
   over([I:R], [M[I] := -1.0e30]),
   over([I:R, K:D], [M[I] := max(M[I], X[I, K])]),
   over([I:R], [S[I] := 0]),
   over([I:R, K:D], [S[I] := S[I] + exp(X[I, K] - M[I])]),
   over([I:R, J:D], [Y[I, J] := exp(X[I, J] - M[I]) / S[I]]).

% mlp(+X, -Y, +S, +D, +H): a transformer MLP block, Y = gelu(X W1 + b1) W2 + b2 + X.
gelu(X, X * (1 / (1 + exp(-1.702 * X)))).
mlp(X, Y, S, D, H) :-
   shape(X, [S, D]), shape(W1, [D, H]), shape(B1, [H]), shape(W2, [H, D]), shape(B2, [D]),
   shape(C1, [S, H]), shape(A, [S, H]), shape(C2, [S, D]), shape(Y, [S, D]),
   over([I:S, J:H], [C1[I, J] := 0]),
   over([I:S, J:H, K:D], [C1[I, J] := C1[I, J] + X[I, K] * W1[K, J]]),
   gelu(C1[I2, J2] + B1[J2], G),
   over([I2:S, J2:H], [A[I2, J2] := G]),
   over([I:S, J:D], [C2[I, J] := 0]),
   over([I:S, J:D, K:H], [C2[I, J] := C2[I, J] + A[I, K] * W2[K, J]]),
   over([I3:S, J3:D], [Y[I3, J3] := C2[I3, J3] + B2[J3] + X[I3, J3]]),
   inputs([W1, B1, W2, B2], _).
inputs(Ns, Ns).

% layer_norm(+X, -Xn, +G, +B, +S, +D): Xn = (X - mean) / sqrt(var + eps) * G + B over the rows.
layer_norm(X, Xn, G, B, S, D) :-
   shape(X, [S, D]), shape(Xn, [S, D]), shape(G, [D]), shape(B, [D]),
   over([I:S], [Mu[I] := 0]),
   over([I:S, J:D], [Mu[I] := Mu[I] + X[I, J]]),
   over([I:S], [Var[I] := 0]),
   over([I:S, K:D], [Var[I] := Var[I] + (X[I, K] - Mu[I] / D) * (X[I, K] - Mu[I] / D)]),
   over([I:S, J:D], [Xn[I, J] := (X[I, J] - Mu[I] / D) / sqrt(Var[I] / D + 1.0e-5) * G[J] + B[J]]).

% vit_block(+X, -Y, +S, +D, +H, +F): a pre-norm transformer encoder block with H heads of
% D // H and an MLP of width F: Y = X2 + MLP(LN2(X2)), X2 = X + Proj(Attention(LN1(X))).
vit_block(X, Y, S, D, H, F) :-
   Dh is D // H, D2 is 2*D, D3 is 3*D, Scale is 1 / sqrt(Dh),
   shape(X, [S, D]), shape(Wqkv, [D, D3]), shape(Bqkv, [D3]), shape(Wo, [D, D]), shape(Bo, [D]),
   shape(W1, [D, F]), shape(B1, [F]), shape(W2, [F, D]), shape(B2, [D]),
   shape(QKV, [S, D3]), shape(QKVb, [S, D3]), shape(Sc, [H, S, S]), shape(P, [H, S, S]), shape(O, [S, D]),
   shape(Pr, [S, D]), shape(X2, [S, D]), shape(C1, [S, F]), shape(A, [S, F]), shape(C2, [S, D]), shape(Y, [S, D]),
   layer_norm(X, Xn, G1, Be1, S, D),
   over([I:S, N:D3], [QKV[I, N] := 0]),
   over([I:S, N:D3, K:D], [QKV[I, N] := QKV[I, N] + Xn[I, K] * Wqkv[K, N]]),
   over([I:S, N:D3], [QKVb[I, N] := QKV[I, N] + Bqkv[N]]),
   over([Hh:H, I:S, J:S], [Sc[Hh, I, J] := 0]),
   over([Hh:H, I:S, J:S, K:Dh], [Sc[Hh, I, J] := Sc[Hh, I, J] + QKVb[I, Hh*Dh + K] * QKVb[J, D + Hh*Dh + K]]),
   over([Hh:H, I:S], [M[Hh, I] := -1.0e30]),
   over([Hh:H, I:S, J:S], [M[Hh, I] := max(M[Hh, I], Sc[Hh, I, J] * Scale)]),
   over([Hh:H, I:S], [Z[Hh, I] := 0]),
   over([Hh:H, I:S, J:S], [Z[Hh, I] := Z[Hh, I] + exp(Sc[Hh, I, J] * Scale - M[Hh, I])]),
   over([Hh:H, I:S, J:S], [P[Hh, I, J] := exp(Sc[Hh, I, J] * Scale - M[Hh, I]) / Z[Hh, I]]),
   over([Hh:H, I:S, K2:Dh], [O[I, Hh*Dh + K2] := 0]),
   over([Hh:H, I:S, K2:Dh, J:S], [O[I, Hh*Dh + K2] := O[I, Hh*Dh + K2] + P[Hh, I, J] * QKVb[J, D2 + Hh*Dh + K2]]),
   over([I:S, N:D], [Pr[I, N] := 0]),
   over([I:S, N:D, K:D], [Pr[I, N] := Pr[I, N] + O[I, K] * Wo[K, N]]),
   over([I:S, N:D], [X2[I, N] := Pr[I, N] + Bo[N] + X[I, N]]),
   layer_norm(X2, Xn2, G2, Be2, S, D),
   over([I:S, J:F], [C1[I, J] := 0]),
   over([I:S, J:F, K:D], [C1[I, J] := C1[I, J] + Xn2[I, K] * W1[K, J]]),
   gelu(C1[I2, J2] + B1[J2], Gelu),
   over([I2:S, J2:F], [A[I2, J2] := Gelu]),
   over([I:S, N:D], [C2[I, N] := 0]),
   over([I:S, N:D, K:F], [C2[I, N] := C2[I, N] + A[I, K] * W2[K, N]]),
   over([I:S, N:D], [Y[I, N] := C2[I, N] + B2[N] + X2[I, N]]),
   inputs([Wqkv, Bqkv, Wo, Bo, W1, B1, W2, B2, G1, Be1, G2, Be2], _).

% scatter(+Idx, +W, -H, +M, +N): H[Idx[k]] += W[k], M sources into N bins: a histogram when N is
% small, an index_add when N is large.
scatter(Idx, W, H, M, N) :-
   shape(Idx, [M]), Hi is N-1, elements(Idx, 0-Hi), shape(W, [M]), shape(H, [N]),
   over([I:N], [H[I] := 0]),
   over([K:M], [H[Idx[K]] := H[Idx[K]] + W[K]]).

% embedding_backward(+Idx, +G, -E, +M, +V, +Dim): E[Idx[k], j] += G[k, j].
embedding_backward(Idx, G, E, M, V, Dim) :-
   shape(Idx, [M]), Hi is V-1, elements(Idx, 0-Hi), shape(G, [M, Dim]), shape(E, [V, Dim]),
   over([I:V, J:Dim], [E[I, J] := 0]),
   over([K:M, J:Dim], [E[Idx[K], J] := E[Idx[K], J] + G[K, J]]).
