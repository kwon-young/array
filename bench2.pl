:- module(bench2, [go/1, go/2, go_chol/1, go_blocked/1, go_scatter/1, go_mlp/1, go_vit/1,
                   matmul/6, softmax/4, cholesky/3, blocked_cholesky/4, batched_cholesky/4, dot/4,
                   scatter/5, embedding_backward/6, mlp/5, layer_norm/6, vit_block/6,
                   bench/6, bench_data/6, bench_stats/7, once_run/4, once_run/5, data/2, names/2, inputs_data/2]).
:- use_module(core2).
:- use_module(compile2).
:- use_module(opencl).
:- set_prolog_flag(stack_limit, 4_000_000_000).

% Kernel time alone: the program is built and the buffers uploaded before the clock starts; a
% run is every kernel launched in order and the queue drained. The best of Reps is reported.

matmul(A, B, C, N, M, P) :-
   shape(A, [N, M]), shape(B, [M, P]), shape(C, [N, P]),
   over([I:N, J:P], [C[I, J] := 0]),
   over([I:N, J:P, K:M], [C[I, J] := C[I, J] + A[I, K] * B[K, J]]).

softmax(X, Y, R, D) :-
   shape(X, [R, D]), shape(Y, [R, D]),
   over([I:R], [M[I] := -1.0e30]),
   over([I:R, K:D], [M[I] := max(M[I], X[I, K])]),
   over([I:R], [S[I] := 0]),
   over([I:R, K:D], [S[I] := S[I] + exp(X[I, K] - M[I])]),
   over([I:R, J:D], [Y[I, J] := exp(X[I, J] - M[I]) / S[I]]).

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

go_chol(Device) :-
   forall(member(N, [32, 64, 256, 1024]),
          ( cholesky(A, L, N), spd(N, As), format(atom(Lb), "cholesky ~d", [N]),
            bench_data(Lb, L, [A-As], Device, [], 3) )),
   forall(member(M-N, [1024-32, 256-64]),
          ( batched_cholesky(A, L, M, N), spd(N, As1), findall(X, ( between(1, M, _), member(X, As1) ), As),
            format(atom(Lb), "cholesky ~dx~d batch", [N, M]),
            bench_data(Lb, L, [A-As], Device, [], 3) )).


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

go_blocked(Device) :-
   forall(member(N-NB, [256-32, 1024-32, 1024-64]),
          ( blocked_cholesky(A, L, N, NB), spd(N, As), format(atom(Lb), "blocked cholesky ~d nb ~d", [N, NB]),
            bench_data(Lb, L, [A-As], Device, [], 3) )).

batched_cholesky(A, L, M, N) :-
   shape(A, [M, N, N]), shape(L, [M, N, N]), shape(C, [M, N]),
   over([B:M, I:N, J:N], [L[B, I, J] := where(J =< I, A[B, I, J], 0)]),
   over([B:M, K:N], [over([I:N], [C[B, I] := where(I =:= K, sqrt(L[B, K, K]), where(K < I, L[B, I, K] / sqrt(L[B, K, K]), 0))]),
                     over([I:N], [L[B, I, K] := where(K =< I, C[B, I], L[B, I, K])]),
                     over([I:N, J:N], [L[B, I, J] := where(K < J, where(J =< I, L[B, I, J] - C[B, I] * C[B, J], L[B, I, J]), L[B, I, J])])]).

% bench_data(+Label, +Out, +Data, +Device, +Options, +Reps): the best kernel time of Reps runs,
% and the memory of the intermediates: the bytes they take, under alloc(arena) the arena, as
% separate buffers apart, the peak live at one kernel, and the time to allocate them.
bench_data(Label, Out, Data, Device, Options0, Reps) :-
   bench_stats(Label, Out, Data, Device, Options0, Reps, S),
   stats{kernels: NK, best: Best, alloc: How, bytes: B, apart: Ap, peak: Pk, setup: Setup} :< S,
   format("~w  ~w  kernels=~d  best=~3f ms  ~w: ~d KB (apart ~d KB, peak ~d KB) in ~3f ms~n",
          [Label, Device, NK, Best*1000, How, B // 1024, Ap // 1024, Pk // 1024, Setup*1000]).

% bench_stats(+Label, +Out, +Data, +Device, +Options, +Reps, -Stats): the figures bench_data/6
% prints, as a dict.
bench_stats(Label, Out, Data, Device, Options0, Reps, Stats) :-
   compile2:device(Device, Dev, Context, Queue),
   device_options(Dev, Derived),
   merge_options(Options0, Derived, Options),
   compile2:kernels(Out, Options, Kernels),
   compile2:source(Kernels, Source),
   compile2:built(Context, Dev, Source, Program),
   compile2:flat_plan(Kernels, Flat), length(Flat, NK),
   findall(Stats0,                                       % the extents bound by the data, as run/4 does
           ( compile2:bind_extents(Kernels, Data),
             compile2:allocate(Context, Queue, Dev, Kernels, Out, Data, Options, Alloc),
             alloc{how: How, buffers: Buffers, bytes: B, apart: Ap, peak: Pk, setup: Setup} :< Alloc,
             once_run(Queue, Program, Buffers, Kernels),           % warm up
             findall(T, ( between(1, Reps, _), once_run(Queue, Program, Buffers, Kernels, T) ), Ts),
             min_list(Ts, Best),
             Stats0 = stats{label: Label, device: Device, kernels: NK, best: Best, alloc: How, bytes: B, apart: Ap,
                            peak: Pk, setup: Setup} ),
           [Stats]).

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

scatter_data(M, N, Is, Ws) :-
   numlist(1, M, Ks), maplist([X, Y]>>(Y is (X * 7919) mod N), Ks, Is), maplist([X, Y]>>(Y is X mod 97), Ks, Ws).

go_scatter(Device) :-
   forall(member(M-N, [1048576-256, 1048576-1048576]),
          ( scatter(Idx, W, H, M, N), scatter_data(M, N, Is, Ws), format(atom(Lb), "scatter ~d into ~d", [M, N]),
            bench_data(Lb, H, [Idx-Is, W-Ws], Device, [], 3) )),
   embedding_backward(Idx2, G, E, 65536, 10000, 64), scatter_data(65536, 10000, Is2, _),
   numlist(1, 4194304, Gs0), maplist([X, Y]>>(Y is X mod 7), Gs0, Gs),
   bench_data('embedding backward 65536x64 into 10000', E, [Idx2-Is2, G-Gs], Device, [], 3).

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

go_vit(Device) :-
   S = 256, D = 768, H = 12, F = 3072,
   vit_block(X, Y, S, D, H, F),
   inputs_data(Y, Data),
   bench_data(vit_block_256x768x12, Y, Data, Device, [], 3), shape(X, _).

go_mlp(Device) :-
   S = 256, D = 768, H = 3072,
   mlp(X, Y, S, D, H),
   inputs_data(Y, Data),
   bench_data(mlp_256x768x3072, Y, Data, Device, [], 3), shape(X, _).

% inputs_data(+Out, -Data): Name-Values for every input of Out's program, from data/2.
inputs_data(Out, Data) :-
   compile2:program(Out, Boxes), names(Boxes, Names),
   include([N]>>(N \== Out, compile2:boxes_of(N, [])), Names, Inputs),
   maplist([In, In-Vals]>>data(In, Vals), Inputs, Data).

dot(A, B, S, N) :-
   shape(A, [N]), shape(B, [N]), shape(S, []),
   over([], [S := 0]),
   over([K:N], [S := S + A[K] * B[K]]).

data(Name, Vals) :-
   shape(Name, Shape), foldl([E, S0, S1]>>(S1 is S0*E), Shape, 1, N),
   numlist(1, N, Is), maplist(datum, Is, Vals).

% Centred, small values: a transformer's activations stay in range, with no denormals, which
% a CPU handles slowly.
datum(I, V) :- V is (float(I mod 97) / 97 - 0.5) * 0.2.

names(Term, Names) :- term_variables(Term, Vs), include([V]>>get_attr(V, core2, _), Vs, Names).

bench(Label, Out, Inputs, Device, Options0, Reps) :-
   maplist([In, In-Vals]>>data(In, Vals), Inputs, Data),
   bench_data(Label, Out, Data, Device, Options0, Reps).

once_run(Queue, Program, Buffers, Kernels) :- once_run(Queue, Program, Buffers, Kernels, _).
once_run(Queue, Program, Buffers, Kernels, T) :-
   get_time(T0),
   compile2:run_plan(Queue, Program, Buffers, [], Kernels),
   cl_finish(Queue),
   get_time(T1), T is T1 - T0.

go(Device) :- go(Device, []).
go(Device, Opts) :-
   matmul(A, B, C, 512, 512, 512), bench('matmul 512^3 ', C, [A, B], Device, Opts, 5),
   matmul(A2, B2, C2, 1024, 1024, 1024), bench('matmul 1024^3', C2, [A2, B2], Device, Opts, 3),
   softmax(X, Y, 1024, 1024), bench('softmax 1024x1024', Y, [X], Device, [local(64)], 5),
   softmax(X2, Y2, 64, 4096), bench('softmax 64x4096 ', Y2, [X2], Device, [local(128)], 5),
   dot(DA, DB, S, 1048576), bench('dot 1M          ', S, [DA, DB], Device, [local(256)], 5).
