:- use_module(core2).
:- use_module(compile2).
:- use_module(opencl, [opencl_device/2, cl_device_info/3]).
:- use_module(bench2, [vit_block/6]).

% The tests are several units, since plunit runs units concurrently: run_tests(all, [jobs(6)]).

% The kernels are checked against the reference on every device, with and without tiles.
near(Xs, Ys) :-
   maplist([X, Y]>>(abs(X - Y) < 1.0e-3 * (1 + abs(X))), Xs, Ys).

matmul(A, B, C, N, M, P) :-
   shape(A, [N, M]), shape(B, [M, P]), shape(C, [N, P]),
   over([I:N, J:P], [C[I, J] := 0]),
   over([I:N, J:P, K:M], [C[I, J] := C[I, J] + A[I, K] * B[K, J]]).

cholesky(A, L, N) :-
   shape(A, [N, N]), shape(L, [N, N]), shape(C, [N]),
   over([I:N, J:N], [L[I, J] := where(J =< I, A[I, J], 0)]),
   over([K:N], [over([I:N], [C[I] := where(I =:= K, sqrt(L[K, K]), where(K < I, L[I, K] / sqrt(L[K, K]), 0))]),
                over([I:N], [L[I, K] := where(K =< I, C[I], L[I, K])]),
                over([I:N, J:N], [L[I, J] := where(K < J, where(J =< I, L[I, J] - C[I] * C[J], L[I, J]), L[I, J])])]).

batched_cholesky(A, L, M, N) :- batched_cholesky(A, L, _, M, N).
batched_cholesky(A, L, C, M, N) :-
   shape(A, [M, N, N]), shape(L, [M, N, N]), shape(C, [M, N]),
   over([B:M, I:N, J:N], [L[B, I, J] := where(J =< I, A[B, I, J], 0)]),
   over([B:M, K:N], [over([I:N], [C[B, I] := where(I =:= K, sqrt(L[B, K, K]), where(K < I, L[B, I, K] / sqrt(L[B, K, K]), 0))]),
                     over([I:N], [L[B, I, K] := where(K =< I, C[B, I], L[B, I, K])]),
                     over([I:N, J:N], [L[B, I, J] := where(K < J, where(J =< I, L[B, I, J] - C[B, I] * C[B, J], L[B, I, J]), L[B, I, J])])]).

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

% gelu(X) as x * sigmoid(1.702 x), with the ops the table has
gelu(X, X * (1 / (1 + exp(-1.702 * X)))).

:- begin_tests(compile2_basics).

test(transpose, [timeout(30), true(V == [1.0, 4.0, 2.0, 5.0, 3.0, 6.0])]) :-
   shape(Y, [2, 3]),
   over([I:3, J:2], [T[I, J] := Y[J, I]]),
   run(T, [Y-[1, 2, 3, 4, 5, 6]], V, []).

test(matmul_matches_reference, [timeout(60), forall((opencl_device(D, _), member(Tile, [1, 4])))]) :-
   matmul(A, B, C, 8, 12, 8),
   numlist(1, 96, As), maplist([X, Y]>>(Y is X mod 7), As, Bs),
   eval(C, [A-As, B-Bs], Ref),
   run(C, [A-As, B-Bs], V, [device(D), tile(Tile)]),
   near(Ref, V).

test(matmul_schedule, [timeout(30)]) :-
   matmul(A, B, C, 8, 12, 8),
   kernels(C, [], [Acc]),
   kernel{par: [_:2, _:2], seq: [_:12, _:4, _:4], priv: [C-[_, _]], names: Names, pre: [_], post: [], temps: []} :< Acc,
   length(Names, 3), forall(member(N, Names), ( member(N1, [A, B, C]), N1 == N )).

test(cumsum_batch_is_parallel, [timeout(30), true(V == [1.0, 2.0, 4.0, 6.0, 9.0, 12.0])]) :-
   shape(X, [3, 2]),
   over([J:2], [C[0, J] := X[0, J]]),
   over([T:2, J:2], [C[T+1, J] := C[T, J] + X[T+1, J]]),
   kernels(C, [tile(1)], [_, Scan]),
   kernel{par: [J1:2], seq: [T1:2], priv: []} :< Scan,
   J1 == J, T1 == T,
   run(C, [X-[1, 2, 3, 4, 5, 6]], V, [tile(1)]).

test(fibonacci_is_sequential, [timeout(30), true(V == [1.0, 1.0, 2.0, 3.0, 5.0, 8.0, 13.0, 21.0])]) :-
   shape(F, [8]),
   over([], [F[0] := 1, F[1] := 1]),
   over([T:6], [F[T+2] := F[T] + F[T+1]]),
   kernels(F, [], [_, Rec]),
   kernel{par: [], seq: [_:6]} :< Rec,
   run(F, [], V, []).

test(source_is_printed, [timeout(30)]) :-
   matmul(A, B, C, 8, 12, 8),
   kernels(C, [], Ks), source(Ks, Src),
   once(sub_string(Src, _, _, _, "__kernel void k0(")),
   once(sub_string(Src, _, _, _, "get_global_id(0)")),
   once(sub_string(Src, _, _, _, "float r_")),
   shape(A, _), shape(B, _).

:- end_tests(compile2_basics).

:- begin_tests(compile2_groups).

test(softmax_is_one_kernel_of_one_group, [timeout(30), forall(opencl_device(D, _))]) :-
   shape(X, [4]),
   over([], [M := -1.0e30]),
   over([K:4], [M := max(M, X[K])]),
   over([I:4], [E[I] := exp(X[I] - M)]),
   over([], [S := 0]),
   over([K:4], [S := S + E[K]]),
   over([I:4], [Y[I] := E[I] / S]),
   kernels(Y, [], [K1]),
   kernel{kind: groups, rows: [], phases: [serial(_), reduce(_, [red(M1, [], max, _)]), serial(_),
                                           reduce(_, [red(S1, [], +, _)]), spread(_, _, _)], names: Ns} :< K1,
   M1 == M, S1 == S, \+ ( member(N, Ns), N == E ),
   Xs = [1, 2, 3, 4],
   eval(Y, [X-Xs], Ref), run(Y, [X-Xs], V, [device(D)]),
   near(Ref, V), sum_list(V, Sum), abs(Sum - 1) < 1.0e-5.

test(batched_softmax_aligns_the_rows, [timeout(30), forall(opencl_device(D, _))]) :-
   shape(X, [3, 5]),
   over([R:3], [M[R] := -1.0e30]),
   over([R:3, K:5], [M[R] := max(M[R], X[R, K])]),
   over([R:3], [S[R] := 0]),
   over([R:3, K:5], [S[R] := S[R] + exp(X[R, K] - M[R])]),
   over([R:3, I:5], [Y[R, I] := exp(X[R, I] - M[R]) / S[R]]),
   kernels(Y, [], [K1]),
   kernel{kind: groups, rows: [R1:3], phases: Phases} :< K1,
   length(Phases, 5), R1 == R,
   numlist(1, 15, Xs0), maplist([A, B]>>(B is (A * 7) mod 11), Xs0, Xs),
   eval(Y, [X-Xs], Ref), run(Y, [X-Xs], V, [device(D), local(8)]),
   near(Ref, V).

test(dot_product_reduces_in_groups, [timeout(30), forall(opencl_device(D, _))]) :-
   shape(A, [1000]), shape(B, [1000]),
   over([], [S := 0]),
   over([K:1000], [S := S + A[K] * B[K]]),
   kernels(S, [local(128)], [K1, K2]),
   kernel{kind: groups, rows: [_:5], phases: [serial(_), reduce(_:200, _)]} :< K1,
   kernel{kind: groups, rows: [], phases: [serial(_), reduce(_:5, _)]} :< K2,
   numlist(1, 1000, As), maplist([X, Y]>>(Y is X mod 3), As, Bs),
   eval(S, [A-As, B-Bs], Ref), run(S, [A-As, B-Bs], V, [device(D), local(128)]),
   near(Ref, V).

test(small_output_reduction_goes_to_groups_large_to_items, [timeout(30)]) :-
   matmul(_, _, C, 8, 12, 8), kernels(C, [], Ks), maplist([K]>>get_dict(kind, K, items), Ks),
   matmul(A2, B2, C2, 4, 12, 8), kernels(C2, [], [K2]), get_dict(kind, K2, groups), shape(A2, _), shape(B2, _),
   kernels(C2, [items(16)], K2s), maplist([K]>>get_dict(kind, K, items), K2s).

:- end_tests(compile2_groups).

:- begin_tests(compile2_staging).

test(matmul_staged_in_local_memory_and_vectorised, [timeout(60), forall(opencl_device(D, _))]) :-
   matmul(A, B, C, 64, 96, 64),
   kernels(C, [], Ks), source(Ks, Src),
   once(sub_string(Src, _, _, _, "__local float s0[")),
   once(sub_string(Src, _, _, _, "barrier(CLK_LOCAL_MEM_FENCE)")),
   once(sub_string(Src, _, _, _, "float4 *")),
   once(sub_string(Src, _, _, _, "#pragma unroll")),
   last(Ks, Acc), kernel{stage: stage(8, 8, Tiles)} :< Acc, length(Tiles, 2),
   numlist(1, 6144, As), maplist([X, Y]>>(Y is (X * 3) mod 7 - 3), As, Bs0), length(Bs, 6144), append(Bs, _, Bs0),
   eval(C, [A-As, B-Bs], Ref), run(C, [A-As, B-Bs], V, [device(D)]),
   near(Ref, V).

test(long_reduction_is_split_over_groups, [timeout(60), forall(opencl_device(D, _))]) :-
   shape(A, [65536]), shape(B, [65536]), shape(S, []),
   over([], [S := 0]),
   over([K:65536], [S := S + A[K] * B[K]]),
   kernels(S, [local(256)], [Partial, Combine]),
   kernel{kind: groups, rows: [_:C], phases: [serial(_), reduce(_:Chunk, _)]} :< Partial,
   kernel{kind: groups, rows: [], phases: [serial(_), reduce(_:C, _)]} :< Combine,
   C * Chunk =:= 65536, C < 64, Chunk >= 256,
   numlist(1, 65536, As), maplist([X, Y]>>(Y is X mod 5 - 2), As, Bs),
   eval(S, [A-As, B-Bs], Ref), run(S, [A-As, B-Bs], V, [device(D), local(256)]),
   near(Ref, V).

test(batched_long_reduction_splits_too, [timeout(60)]) :-
   shape(X, [4, 8192]), shape(M, [4]),
   over([R:4], [M[R] := -1.0e30]),
   over([R:4, K:8192], [M[R] := max(M[R], X[R, K])]),
   kernels(M, [], [Partial, Combine]),
   kernel{kind: groups, rows: [_:C, _:4]} :< Partial,
   kernel{kind: groups, rows: [_:4], phases: [serial(_), reduce(_:C, [red(_, _, max, _)])]} :< Combine,
   C * 4 < 64,
   numlist(1, 32768, Xs0), maplist([A, B]>>(B is (A * 37) mod 1009), Xs0, Xs),
   eval(M, [X-Xs], Ref), run(M, [X-Xs], V, []),
   near(Ref, V).

test(device_options_fit_the_device_and_run, [timeout(120), forall(opencl_device(D, Dev))]) :-
   device_options(Dev, Opts),
   option(vector(W), Opts), option(group(G), Opts), option(stage(TK), Opts), option(local(L), Opts),
   option(tile([TI, TJ]), Opts), TJ =:= 2*W, G*G =< 1024, L /\ (L-1) =:= 0,
   cl_device_info(Dev, local_mem_size, Bytes), (G*TI + G*TJ)*TK*4 =< Bytes,
   matmul(A, B, C, 64, 96, 64),
   numlist(1, 6144, As), maplist([X, Y]>>(Y is (X * 3) mod 7 - 3), As, Bs0), length(Bs, 6144), append(Bs, _, Bs0),
   eval(C, [A-As, B-Bs], Ref), run(C, [A-As, B-Bs], V, [device(D)]),
   near(Ref, V).

test(cpu_matmul_is_packed_per_thread, [timeout(120), forall((opencl_device(D, Dev), cl_device_info(Dev, type, cpu)))]) :-
   device_options(Dev, Opts),
   matmul(A, B, C, 128, 256, 128),
   kernels(C, Opts, Ks), last(Ks, Acc),
   kernel{stage: pack(Threads, KC, MCT, NS, _, Tiles)} :< Acc,
   length(Tiles, 2), Threads >= 1, KC >= 2, MCT >= 1, NS >= 1,
   source(Ks, Src), once(sub_string(Src, _, _, _, "int t = get_global_id(0)")), \+ sub_string(Src, _, _, _, "barrier"),
   numlist(1, 32768, As), maplist([X, Y]>>(Y is (X * 5) mod 11 - 5), As, Bs),
   eval(C, [A-As, B-Bs], Ref), run(C, [A-As, B-Bs], V, [device(D)]),
   near(Ref, V).

% The attention matmuls of a transformer: the scores of each head, a batch axis before the
% strips, and the heads' products with the values, whose target mixes the head and its slice.
test(attention_matmuls_stage_per_head, [timeout(90), forall(opencl_device(D, _))]) :-
   H = 2, S = 16, Dh = 16, DM is H*Dh, Opts = [tile([8, 8]), group(2), stage(8)],
   shape(Q, [S, DM]), shape(Kt, [S, DM]), shape(Sc, [H, S, S]), shape(P, [H, S, S]), shape(V, [S, DM]), shape(O, [S, DM]),
   over([Hh:H, I:S, J:S], [Sc[Hh, I, J] := 0]),
   over([Hh:H, I:S, J:S, K:Dh], [Sc[Hh, I, J] := Sc[Hh, I, J] + Q[I, Hh*Dh + K] * Kt[J, Hh*Dh + K]]),
   over([Hh:H, I:S, K2:Dh], [O[I, Hh*Dh + K2] := 0]),
   over([Hh:H, I:S, K2:Dh, J:S], [O[I, Hh*Dh + K2] := O[I, Hh*Dh + K2] + P[Hh, I, J] * V[J, Hh*Dh + K2]]),
   kernels(Sc, Opts, [Ka]), kernel{par: [_:2, _:2, _:2], stage: stage(2, 8, [_, _]), pre: [_]} :< Ka,
   kernels(O, Opts, [Kb]), kernel{par: [_:2, _:2, _:2], stage: stage(2, 8, [_, _]), pre: [_]} :< Kb,
   numlist(1, 512, Ns), maplist([X, Y]>>(Y is (X * 7) mod 11 / 11 - 0.5), Ns, Qs), maplist([X, Y]>>(Y is (X * 5) mod 13 / 13 - 0.5), Ns, Ks),
   eval(Sc, [Q-Qs, Kt-Ks], Ref1), run(Sc, [Q-Qs, Kt-Ks], V1, [device(D) | Opts]), near(Ref1, V1),
   eval(O, [P-Qs, V-Ks], Ref2), run(O, [P-Qs, V-Ks], V2, [device(D) | Opts]), near(Ref2, V2).

:- end_tests(compile2_staging).

:- begin_tests(compile2_cholesky).

test(cholesky_is_one_sweep_kernel, [timeout(300), forall(opencl_device(D, _))]) :-
   cholesky(A, L, 64),
   kernels(L, [], [_, Sweep]),
   kernel{kind: groups, rows: [], phases: [loop(K1, 64, [spread(_, _, _), spread(_, _, _), spread([_, _], [_, _], _)])]} :< Sweep,
   K1 == K1,
   findall(V, ( between(0, 63, I), between(0, 63, J), V is min(I, J) + 1 ), As),
   eval(L, [A-As], Ref), run(L, [A-As], Vals, [device(D)]),
   near(Ref, Vals),
   nth0(0, Vals, V00), abs(V00 - 1) < 1.0e-4, nth0(4095, Vals, V), abs(V - 1) < 1.0e-3.

test(blocked_cholesky_stages_the_trailing_update, [timeout(300), forall(opencl_device(D, _))]) :-
   blocked_cholesky(A, L, 128, 32),
   kernels(L, [], [_, loop(_, 4, [Panel, Copy, Solve, Copy2, Update])]),
   kernel{kind: groups, phases: [loop(_, 32, _)]} :< Panel,
   kernel{kind: items, stage: none} :< Copy, kernel{kind: items, stage: none} :< Copy2,
   kernel{kind: items, par: [_:128], local: [S1], tiles: []} :< Solve, var(S1),
   kernel{kind: items, stage: stage(_, _, _), ranges: [_, _]} :< Update,
   findall(V, ( between(0, 127, I), between(0, 127, J), V is min(I, J) + 1 ), As),
   eval(L, [A-As], Ref), run(L, [A-As], Vals, [device(D)]),
   near(Ref, Vals).

test(batched_cholesky_is_a_group_per_matrix, [timeout(300), forall(opencl_device(D, _))]) :-
   batched_cholesky(A, L, C, 4, 32),
   kernels(L, [], [_, Sweep]),
   kernel{kind: groups, rows: [B1:4], phases: [loop(_, 32, _)], shared: Shared} :< Sweep, var(B1),
   member(L1-1-1024, Shared), L1 == L, member(C1-1-32, Shared), C1 == C,
   source([Sweep], Src), once(sub_string(Src, _, _, _, "__local float s_")), \+ sub_string(Src, _, _, _, "GLOBAL_MEM_FENCE"),
   findall(V, ( between(0, 3, _), between(0, 31, I), between(0, 31, J), V is min(I, J) + 1 ), As),
   eval(L, [A-As], Ref), run(L, [A-As], Vals, [device(D)]),
   near(Ref, Vals).

% A step of a 4x4 factor has 4 parallel points, under the lanes a group occupies: each matrix
% is one work item, with no barrier; with lanes(1) it is a group, as before.
test(tiny_batched_cholesky_is_an_item_per_matrix, [timeout(300), forall(opencl_device(D, _))]) :-
   batched_cholesky(A, L, C, 64, 4),
   kernels(L, [], [_, Sweep]),
   kernel{kind: groups, rows: [_:64], phases: [loop(_, 4, _)], item: true, local: 1, shared: []} :< Sweep,
   source([Sweep], Src), once(sub_string(Src, _, _, _, "get_global_id(0)")), \+ sub_string(Src, _, _, _, "barrier"),
   kernels(L, [lanes(1)], [_, Group]), \+ get_dict(item, Group, _),
   findall(V, ( between(0, 63, _), between(0, 3, I), between(0, 3, J), V is min(I, J) + 1 ), As),
   eval(L, [A-As], Ref), run(L, [A-As], Vals, [device(D)]),
   near(Ref, Vals), shape(C, _).

% A chain of two reductions of length 2 cannot fill a warp: it goes to kernels of work items,
% a group only when the lanes are 1.
test(short_reductions_stay_items, [timeout(300), forall(opencl_device(D, _))]) :-
   shape(X, [64, 2, 2]), shape(Y, [64, 2]), shape(G, [64, 2]), shape(H, [64, 2]),
   over([B:64, I:2], [G[B, I] := 0]),
   over([B:64, I:2, K:2], [G[B, I] := G[B, I] + X[B, I, K] * Y[B, K]]),
   over([B:64, I:2], [H[B, I] := 0]),
   over([B:64, I:2, K:2], [H[B, I] := H[B, I] + G[B, I] * Y[B, K]]),
   kernels(H, [], Items), forall(member(K1, Items), get_dict(kind, K1, items)),
   kernels(H, [lanes(1)], [Group]), kernel{kind: groups, local: 1} :< Group,
   numlist(1, 256, Ns), maplist([N, V]>>(V is (N mod 5) - 2), Ns, Xs), length(Ys, 128), maplist([V]>>(V = 1), Ys),
   eval(H, [X-Xs, Y-Ys], Ref), run(H, [X-Xs, Y-Ys], Vals, [device(D)]), near(Ref, Vals),
   run(H, [X-Xs, Y-Ys], Vals1, [device(D), lanes(1)]), near(Ref, Vals1).

% A box reading what the chain wrote outside its own row ends the chain: the second product
% reads G at every K of its row, which other groups write. Grouped, it read them unfinished.
test(chain_reads_its_own_row_only, [timeout(300), forall(opencl_device(D, _))]) :-
   shape(X, [64, 2, 2]), shape(Y, [64, 2, 2]), shape(G, [64, 2, 2]), shape(H, [64, 2, 2]),
   over([B:64, I:2, J:2], [G[B, I, J] := 0]),
   over([B:64, I:2, J:2, K:2], [G[B, I, J] := G[B, I, J] + X[B, I, K] * Y[B, K, J]]),
   over([B:64, I:2, J:2], [H[B, I, J] := 0]),
   over([B:64, I:2, J:2, K:2], [H[B, I, J] := H[B, I, J] + G[B, I, K] * Y[B, K, J]]),
   kernels(H, [lanes(1)], Ks), length(Ks, 2), forall(member(K1, Ks), get_dict(kind, K1, items)),
   numlist(1, 256, Ns), maplist([N, V]>>(V is (N mod 5) - 2), Ns, Xs), maplist([N, V]>>(V is (N mod 3) - 1), Ns, Ys),
   eval(H, [X-Xs, Y-Ys], Ref), run(H, [X-Xs, Y-Ys], Vals, [device(D), lanes(1)]), near(Ref, Vals).

:- end_tests(compile2_cholesky).

:- begin_tests(compile2_scatter).

test(scatter_add_is_atomic, [timeout(120), forall(opencl_device(D, _))]) :-
   shape(Idx, [4096]), elements(Idx, 0-15), shape(W, [4096]), shape(H, [16]),
   over([I:16], [H[I] := 0]),
   over([K:4096], [H[Idx[K]] := H[Idx[K]] + W[K]]),
   kernels(H, [], [_, Scatter]),
   kernel{kind: items, par: [_:_], atomics: [H1-(+)]} :< Scatter, H1 == H,
   source([Scatter], Src), once(sub_string(Src, _, _, _, "atomic_add_float(")),
   numlist(1, 4096, Ks), maplist([X, Y]>>(Y is (X * 7) mod 16), Ks, Is), maplist([X, Y]>>(Y is X mod 5), Ks, Ws),
   eval(H, [Idx-Is, W-Ws], Ref), run(H, [Idx-Is, W-Ws], V, [device(D)]),
   near(Ref, V).

test(embedding_backward_scatters_rows, [timeout(120), forall(opencl_device(D, _))]) :-
   shape(Idx, [512]), elements(Idx, 0-63), shape(G, [512, 32]), shape(E, [64, 32]),
   over([I:64, J:32], [E[I, J] := 0]),
   over([K:512, J:32], [E[Idx[K], J] := E[Idx[K], J] + G[K, J]]),
   kernels(E, [], [_, Scatter]),
   kernel{kind: items, par: [_, _], atomics: [E1-(+)]} :< Scatter, E1 == E,
   numlist(1, 512, Ks), maplist([X, Y]>>(Y is (X * 13) mod 64), Ks, Is),
   numlist(1, 16384, Gs0), maplist([X, Y]>>(Y is X mod 7), Gs0, Gs),
   eval(E, [Idx-Is, G-Gs], Ref), run(E, [Idx-Is, G-Gs], V, [device(D)]),
   near(Ref, V).

:- end_tests(compile2_scatter).

:- begin_tests(compile2_fusion).

test(matmul_with_epilogue_is_one_kernel, [timeout(120), forall(opencl_device(D, _))]) :-
   shape(X, [64, 96]), shape(W, [96, 64]), shape(B, [64]), shape(R, [64, 64]), shape(C, [64, 64]), shape(Y, [64, 64]),
   over([I:64, J:64], [C[I, J] := 0]),
   over([I:64, J:64, K:96], [C[I, J] := C[I, J] + X[I, K] * W[K, J]]),
   gelu(C[I2, J2] + B[J2], G),
   over([I2:64, J2:64], [Y[I2, J2] := G + R[I2, J2]]),
   kernels(Y, [], [K1]),
   kernel{kind: items, pre: [_], post: [_], temps: [C1]} :< K1, C1 == C,
   source([K1], Src), \+ sub_string(Src, _, _, _, "__global float *v0, __global float *v1, __global float *v2, __global float *v3, __global float *v4, __global float *v5"),
   numlist(1, 6144, Xs0), maplist([A, V]>>(V is (A mod 13) / 13), Xs0, Xs), maplist([A, V]>>(V is ((A * 3) mod 7) / 7 - 0.5), Xs0, Ws),
   numlist(1, 64, Bs0), maplist([A, V]>>(V is A / 64), Bs0, Bs), numlist(1, 4096, Rs0), maplist([A, V]>>(V is (A mod 5) / 5), Rs0, Rs),
   eval(Y, [X-Xs, W-Ws, B-Bs, R-Rs], Ref), run(Y, [X-Xs, W-Ws, B-Bs, R-Rs], Vals, [device(D)]),
   near(Ref, Vals).

test(pure_names_stay_buffers_under_a_reduction, [timeout(60)]) :-
   shape(X, [64, 64]), shape(W, [64, 64]), shape(C, [64, 64]),
   over([I:64, J:64], [E[I, J] := exp(X[I, J])]),
   over([I:64, J:64], [C[I, J] := 0]),
   over([I:64, J:64, K:64], [C[I, J] := C[I, J] + E[I, K] * W[K, J]]),
   kernels(C, [], Ks), length(Ks, 2), last(Ks, Acc), kernel{stage: stage(_, _, _)} :< Acc.

test(recurrence_with_a_local_name, [timeout(30), forall(opencl_device(D, _))]) :-
   % x(t+1) = F x(t), F a rotation, P the loop-local product, B a batch of trajectories
   shape(F, [2, 2]), shape(X, [B, 5, 2]), B = 3,
   over([Bi:B, T:4], [over([I:2], [P[I] := 0]),
                      over([I:2, J:2], [P[I] := P[I] + F[I, J] * X[Bi, T, J]]),
                      over([I:2], [X[Bi, T+1, I] := P[I]])]),
   kernels(X, [tile(1)], [K]),
   kernel{par: [B1:3], seq: [T1:4], local: [P1]} :< K,
   B1 == Bi, T1 == T, P1 == P,
   Fs = [0, -1, 1, 0], Xs = [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0],
   eval(X, [F-Fs, X-Xs], Ref), run(X, [F-Fs, X-Xs], V, [device(D)]),
   near(Ref, V).

% A transformer encoder block is nine kernels: two layer norms and the softmax as work-group
% chains, the six matmuls with their initialisations and epilogues fused, bias, residual,
% gelu, the head's scale folded into the softmax.
test(vit_block_is_nine_kernels, [timeout(120), forall(opencl_device(D, _))]) :-
   S = 16, Dm = 32, H = 2, F = 64, Opts = [tile([8, 8]), group(2), stage(8), local(32), items(8), lanes(2)],
   vit_block(X, Y, S, Dm, H, F),
   kernels(Y, Opts, Ks), length(Ks, 9),
   include([K]>>get_dict(kind, K, groups), Ks, Gs), length(Gs, 3),
   include([K]>>(get_dict(stage, K, stage(_, _, _)), get_dict(pre, K, [_])), Ks, Ms), length(Ms, 6),
   compile2:program(Y, Boxes), bench2:names(Boxes, Names),
   include([N]>>(N \== Y, compile2:boxes_of(N, [])), Names, Inputs),
   maplist([N, N-Vs]>>( shape(N, Sh), compile2:size(Sh, Len), numlist(1, Len, Is),
                        maplist([I, V]>>(V is ((I * 7) mod 23) / 23 - 0.5), Is, Vs) ), Inputs, Data),
   eval(Y, Data, Ref), run(Y, Data, V, [device(D) | Opts]),
   near(Ref, V), shape(X, _).

:- end_tests(compile2_fusion).
