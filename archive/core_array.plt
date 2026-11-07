:- use_module(core_array).
:- begin_tests(core_array).
x(input(x, [2, 3], int, 0-5), [x-[0, 1, 2, 3, 4, 5]]).
z(input(z, [5], int, 5-9), [z-[5, 6, 7, 8, 9]]).
dot(Acc, Y) :- A = input(a, [256], int, -128-127), B = input(b, [256], int, -128-127),
   over([], agg(Acc, K:256, A[K] * B[K]), Y).
fdot(In, Acc, Y) :- X = input(x, [64], float, 0-1), W = input(w, [64], float, -1-1),
   over([], agg(Acc, K:64, cast(In, X[K]) * cast(In, W[K])), Y).
test(fusion, [timeout(10)]) :- x(X, D), transpose(X, T), reshape(T, [6], R), lower(out, R, [kernel(out, [6], K)]), eval(R, D, V),
   K =@= for(par, I, 6, store(out, I, load(x, I mod 2*3 + I//2 mod 3))), V == [0, 3, 1, 4, 2, 5].
test(shapes_are_relations, [timeout(10), true(N == 3)]) :-
   reshape(input(y, [12], int, 0-1), [N, 4], _), x(X, _), \+ matmul(X, X, _).
test(matmul, [timeout(10), true(V == [5, 14, 14, 50])]) :- x(X, D), transpose(X, T), matmul(X, T, C), eval(C, D, V).
test(gather, [timeout(10), true(V == [9, 5, 7])]) :-
   z(Z, D), take(Z, input(i, [3], int, 0-4), G), info(G, int, _, _), eval(G, [i-[4, 0, 2] | D], V).
test(slice, [timeout(10), true(V == [6, 8])]) :- z(Z, D), slice(Z, 1:5:2, S), eval(S, D, V).
test(ranges, [timeout(10), true(Rs == [0-9, 5-9, 0-16, 0-2])]) :- z(Z, _), pad(Z, 2-2, P), shrink(P, 2-7, S),
   over([I:5], I*I, Q), over([J:6], J mod 3, M), maplist([A, R]>>info(A, _, R, _), [P, S, Q, M], Rs).
test(kinds, [timeout(10), true(Ks == [float, bool, int])]) :- z(Z, _), over([I], Z[I]*0.5, A),
   over([J], Z[J] < 7, B), over([L], where(Z[L] < 7, Z[L], 0), C), maplist([X, K]>>info(X, K, _, _), [A, B, C], Ks).
test(kinds_backwards, [timeout(10)]) :-
   over([I], input(y, [3], K, 0-9)[I] * 2, A), info(A, int, _, _), \+ K = float.
test(out_of_bounds, [timeout(10), error(domain_error(in_bounds, _))]) :- z(Z, _), over([I:4], Z[I*2], A), info(A, _, _, _).
test(batched_scan, [timeout(10), true(V == [1, 2, 4, 6, 9, 12])]) :- W = input(w, [3, 2], int, 1-6),
   C = rec(S, [T:3, J:2], where(T =:= 0, W[0, J], S[T-1, J] + W[T, J])),
   batch(C, [B:_], []), B == J, lower(out, C, [kernel(_, _, for(par, J1, 2, for(seq, T1, 3, _)))]), J1 == J, T1 == T,
   eval(C, [w-[1, 2, 3, 4, 5, 6]], V).
test(sequential_scan, [timeout(10), true(V == [1, 2, 2, 1, 1, 2])]) :- M = input(m, [2, 2], int, 0-1),
   C = rec(S, [T:3, I:2], where(T =:= 0, input(v, [2], int, 1-2)[I], agg(+, K:2, M[I, K] * S[T-1, K]))),
   batch(C, [], [_]), lower(out, C, [kernel(_, _, for(seq, _, 3, _))]), eval(C, [m-[0, 1, 1, 0], v-[1, 2]], V).
test(fold, [timeout(10), true(V-Ns == [9, 12]-[b0, out])]) :- W = input(w, [3, 2], int, 1-6),
   fold(rec(S, [T:3, J:2], where(T =:= 0, W[0, J], S[T-1, J] + W[T, J])), F),
   info(F, _, _, _), lower(out, F, Ks), maplist(arg(1), Ks, Ns), eval(F, [w-[1, 2, 3, 4, 5, 6]], V).
test(views_are_bounded, [timeout(10), error(domain_error(in_bounds, _))]) :-
   z(Z, _), over([I:3], Z[I], P), over([J:3], P[J+2], Q), info(Q, _, _, _).
test(chains_are_buffered, [timeout(10), true(V-Ns == [221, 770, 770, 2696]-[b0, out])]) :- x(X, D), transpose(X, T),
   matmul(X, T, G), matmul(G, G, G2), lower(out, G2, Ks), maplist(arg(1), Ks, Ns), eval(G2, D, V).
test(buffers_are_shared, [timeout(10), true(V-Ns == [11885, 41594, 41594, 145580]-[b0, b1, out])]) :- x(X, D),
   transpose(X, T), matmul(X, T, G), matmul(G, G, G2), matmul(G2, G, G3), lower(out, G3, Ks), maplist(arg(1), Ks, Ns),
   eval(G3, D, V).
test(exact_ints, [timeout(30), true(Acc-E == int32-0)]) :- dot(+, Y0), info(Y0, int, _, 0),
   dot(int16, Y1), \+ info(Y1, _, _, _), dot(bf16, Y2), info(Y2, _, _, E2), E2 > 0, dot(Acc, Y), choose([Acc], Y, 0),
   info(Y, _, _, E).
test(float_dot, [timeout(30), true(In-Acc == fp16-fp32)]) :- fdot(fp32, fp32, Y0), info(Y0, float, -64-64, E0),
   fdot(bf16, bf16, Y1), info(Y1, _, _, E1), E0 < 0.001, E1 > 1, fdot(In, Acc, Y), choose([In, Acc], Y, 0.1).
test(error_rules, [timeout(10), true((Es = [R, S, I], R =:= 2** -8, S =:= 1, I =:= inf))]) :- X = input(x, [4], float, 0-1),
   over([I], max(cast(bf16, X[I]) - 0.5, 0), Relu), over([J], where(0.5 < cast(bf16, X[J]), X[J], 0), Step),
   over([K], 1 / cast(fp16, X[K]), Inv), maplist([A, E]>>info(A, _, _, E), [Relu, Step, Inv], Es).
test(no_bound_in_recs, [timeout(10), fail]) :- W = input(w, [3], float, 0-1),
   fold(rec(S, [T:3], where(T =:= 0, W[0], cast(fp16, S[T-1] + W[T]))), F), info(F, _, _, _).
test(casts_are_lowered, [timeout(10), true(V == [0.5])]) :- X = input(x, [1], float, 0-1), over([I], cast(fp16, X[I]), A),
   lower(out, A, [kernel(out, [1], for(par, _, 1, store(out, _, cast(fp16, load(x, _)))))]), eval(A, [x-[0.5]], V).
:- end_tests(core_array).
