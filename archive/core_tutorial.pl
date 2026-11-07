/* A tour of core_array.pl. Load it with

     ~/prog/swipl-devel/install/bin/swipl core_tutorial.pl

   and paste the queries below at the top level.
*/
:- use_module(core_array).

% Sample inputs. An input declares the kind and the range of its elements, its data is apart:
% x is [[0, 1, 2], [3, 4, 5]] and z is [5, 6, 7, 8, 9].
x(input(x, [2, 3], int, 0-5)).
z(input(z, [5], int, 5-9)).
% dot(?Acc, -Y): the dot product of two vectors of 256 int8 values, summed in the format Acc.
dot(Acc, Y) :- A = input(a, [256], int, -128-127), B = input(b, [256], int, -128-127),
   over([], agg(Acc, K:256, A[K] * B[K]), Y).
% fdot(?In, ?Acc, -Y): the dot product of two vectors of 64 reals, read in the format In, summed in Acc.
fdot(In, Acc, Y) :- X = input(x, [64], float, 0-1), W = input(w, [64], float, -1-1),
   over([], agg(Acc, K:64, cast(In, X[K]) * cast(In, W[K])), Y).
data([x-[0, 1, 2, 3, 4, 5], z-[5, 6, 7, 8, 9]]).

% run(+A, -Vals): the elements of A computed from the sample data, row-major.
run(A, Vals) :- data(D), eval(A, D, Vals).
% show(+A): prints the kernels computing A, in order, the last one into the buffer out.
show(A) :- lower(out, A, Ks), forall(member(K, Ks), portray_clause(K)).

/* 1. An array is a term: a function from an index box to values
   -------------------------------------------------------------
   A transpose is an array whose element at [I, J] is the element of x at [J, I]: X[J, I],
   with the block operator [] that core_array exports. As [] is then an operator, the top
   level prints an empty list as ([]).

   ?- x(X), transpose(X, T).
   ?- x(X), transpose(X, T), run(T, V).
   V = [0, 3, 1, 4, 2, 5].

2. Composing never clashes: reading an array is substituting into its body
   --------------------------------------------------------------------------
   A transpose then a reshape is a single kernel with a single load: the reshape's div/mod
   index is composed into the transpose, there is no stack of views.

   ?- x(X), transpose(X, T), reshape(T, [6], R), show(R).
   kernel(out, [6], for(par, A, 6, store(out, A, load(x, A mod 2*3+A//2 mod 3)))).

   A reshape back to [2, 3] is still one load:

   ?- x(X), transpose(X, T), reshape(T, [6], R), reshape(R, [2, 3], R2), run(R2, V).
   V = [0, 3, 1, 4, 2, 5].

   Substituting is not always a win: a read under an agg of an array that sums itself would redo
   that sum at each step of the outer one. Such an array is stored in a buffer of its own, b0,
   and computed once. A product of Gram matrices is two kernels, one buffer read twice:

   ?- x(X), transpose(X, T), matmul(X, T, G), matmul(G, G, G2), show(G2), run(G2, V).
   V = [221, 770, 770, 2696].

   One table of buffers serves the whole program: an array met again, anywhere, is the same
   buffer. G3 reads G2 and G, G2 reads G too, and G is still computed once: three kernels.

   ?- x(X), transpose(X, T), matmul(X, T, G), matmul(G, G, G2), matmul(G2, G, G3), show(G3), run(G3, V).
   V = [11885, 41594, 41594, 145580].

3. New ops are one over/3 away
   ---------------------------
   over(Dims, Expr, A) names the dims with Prolog variables: the same variable is the
   same dim, a missing one broadcasts, agg(+, K:N, E) sums over K. Where a dim is an index,
   a dim written D takes the size of what it indexes, and a dim written D:N stays in bounds.

   Indexing, slicing and striding are reads at index expressions:

   ?- z(Z), over([I:4], Z[I], P), run(P, V).
   V = [5, 6, 7, 8].
   ?- x(X), over([J], X[1, J], P), run(P, V).
   V = [3, 4, 5].
   ?- z(Z), over([I:2], Z[1 + I*2], P), run(P, V).
   V = [6, 8].
   ?- z(Z), over([I:6], Z[I], P).
   false.

   slice/3 is numpy's start:stop:step, sizing the dim itself:

   ?- z(Z), slice(Z, 0:5:2, S), run(S, V), show(S).
   V = [5, 7, 9].

   The diagonal of a Gram matrix: the matmul is fused into the diagonal.

   ?- x(X), transpose(X, T), matmul(X, T, G), over([I], G[I, I], D), run(D, V), show(D).
   V = [5, 50].

   An outer product, a flip and a sliding sum (a 1D convolution):

   ?- z(Z), over([I, J], Z[I] * Z[J], P), run(P, V).
   ?- z(Z), over([I:5], Z[4-I], F), run(F, V).
   V = [9, 8, 7, 6, 5].
   ?- z(Z), over([I:3], agg(+, K:3, Z[I+K]), C), run(C, V).
   V = [18, 21, 24].

   A dim is a value too: an arange is just its dim.

   ?- over([I:6], I mod 3, A), run(A, V).
   V = [0, 1, 2, 0, 1, 2].

4. Shapes are relations
   --------------------
   Sizes are clpBNR integers: they can be unknown and be solved backwards.

   ?- reshape(input(y, [12], int, 0-1), [N, 4], _).
   N = 3.
   ?- reshape(input(y, [12], int, 0-1), [N, M], _), N = 2.
   N = 2, M = 6.

   A matmul unifies the sizes of the dim it sums over: mismatched shapes fail.

   ?- matmul(input(a, [2, K], int, 0-1), input(b, [3, M], int, 0-1), C), shape(C, S).
   K = 3, S = [2, M].
   ?- x(X), matmul(X, X, _).
   false.

5. One network: index arithmetic, conditions, ranges and kinds
   -----------------------------------------------------------
   info(A, Kind, Lo-Hi, Err) analyses a generic element of A: its dims are clpBNR integers, its
   conditions booleans, its values reals and its kinds integers, all in one network. Err, a bound
   on its rounding error, is the subject of section 7: below, nothing rounds and Err is 0.

   5.1 Every read is proved in bounds. A strided read past the end is caught:

   ?- z(Z), over([I:4], Z[I*2], A), info(A, K, R, _).
   ERROR: Domain error: `in_bounds' expected, found `input(z,[5],int,5-9)[_A{integer(0,3)}*2]'
   ?- z(Z), over([I:3], Z[I*2], A), info(A, K, R, _).
   K = int, R = 5-9.

   A read of an array is proved in its own box, not only in the box of the inputs it reads:
   P is the first 3 elements of z, and reading it at 4 is caught although z[4] exists.

   ?- z(Z), over([I:3], Z[I], P), over([J:3], P[J+2], Q), info(Q, K, R, _).
   ERROR: Domain error: `in_bounds' expected, found `array([_A:3],input(z,[5],int,5-9)[_A])[_B{integer(0,2)}+2]'

   A read is proved under the conditions of the wheres above it: the pad reads z at I-2,
   which is in bounds only because its conditions guard it.

   ?- z(Z), pad(Z, 2-2, P), info(P, K, R, _).
   K = int, R = 0-9.

   A gather is proved by the range its index array declares:

   ?- z(Z), take(Z, input(i, [3], int, 0-4), G), info(G, K, R, _), show(G).
   K = int, R = 5-9.
   ?- z(Z), take(Z, input(i, [3], int, 0-9), G), info(G, K, R, _).
   ERROR: Domain error: `in_bounds' expected, found `input(z,[5],int,5-9)[input(i,[3],int,0-9)[_A{integer(0,2)}]]'

   5.2 Ranges. A condition on indices is decided when their bounds decide it: shrinking the
   padding away leaves no 0, keeping one element of padding keeps it.

   ?- z(Z), pad(Z, 2-2, P), shrink(P, 2-7, S), info(S, _, R, _), show(S).
   R = 5-9.
   ?- z(Z), pad(Z, 2-2, P), shrink(P, 1-6, S), info(S, _, R, _), run(S, V).
   R = 0-9, V = [0, 5, 6, 7, 8].
   ?- over([I:6], I mod 3, A), info(A, K, R, _).
   K = int, R = 0-2.
   ?- over([I:6], I*I, A), info(A, K, R, _).
   K = int, R = 0-25.

   A condition on data is not decided: its range is the hull of both branches.

   ?- x(X), over([I, J], where(2 < X[I, J], X[I, J], 0), Relu), info(Relu, K, R, _).
   K = int, R = 0-5.

   5.3 Kinds: bool < int < float, the largest of the operands, a comparison is a bool and
   arithmetic on bools is on ints.

   ?- z(Z), over([I], Z[I] * 0.5, A), info(A, K, _, _).
   K = float.
   ?- z(Z), over([I], Z[I] < 7, A), info(A, K, R, _).
   K = bool, R = 0-1.
   ?- z(Z), over([I], (Z[I] < 7) + (Z[I] < 8), A), info(A, K, R, _).
   K = int, R = 0-2.
   ?- z(Z), over([I], sin(Z[I]), A), info(A, K, _, _).
   K = float.

   Kinds are relations too: an unknown kind is narrowed by what the result must be.

   ?- over([I], input(y, [3], Ky, 0-1)[I], A), info(A, bool, _, _).
   Ky = bool.
   ?- over([I], input(y, [3], Ky, 0-9)[I] * 2, A), info(A, int, _, _), Ky = float.
   false.

6. Recurrences
   -----------
   rec(S, [T:N | Dims], E) is the array S whose element at T is E, which may read S at
   an earlier T. The cumulative sum of x along its dim 0:

   ?- x(X), C = rec(S, [T:2, J:3], where(T =:= 0, X[0, J], S[T-1, J] + X[T, J])), run(C, V).
   V = [0, 1, 2, 3, 5, 7].

   Its dim J is a batch: every read of S keeps J. Nobody declared it, and the kernel runs
   the batch in parallel around the sequence of steps.

   ?- x(X), C = rec(S, [T:2, J:3], where(T =:= 0, X[0, J], S[T-1, J] + X[T, J])),
      batch(C, Batch, Others), show(C).
   Batch = [J:3], Others = ([]).

   A fold is the last state of a rec: an array reading a rec, so two kernels, the rec into a
   buffer b0 of its own, then the fold reading it.

   ?- x(X), C = rec(S, [T:2, J:3], where(T =:= 0, X[0, J], S[T-1, J] + X[T, J])),
      fold(C, F), show(F), run(F, V).
   V = [3, 5, 7].

   Fibonacci reads two steps back; the read of T-2 only happens where T >= 2.

   ?- Fib = rec(S, [T:8], where(T < 2, 1, S[T-1] + S[T-2])), run(Fib, V), show(Fib).
   V = [1, 1, 2, 3, 5, 8, 13, 21].

   A matrix-vector recurrence reads its state at K, a dim it sums over: no batch dim,
   the steps are sequential and the elements of a step parallel.

   ?- M = input(m, [2, 2], int, 0-1), V0 = input(v, [2], int, 0-1),
      C = rec(S, [T:4, I:2], where(T =:= 0, V0[I], agg(+, K:2, M[I, K]*S[T-1, K]))),
      batch(C, Batch, _), eval(C, [m-[1, 1, 1, 0], v-[1, 0]], V), show(C).
   Batch = ([]), V = [1, 0, 1, 1, 2, 1, 3, 2].

7. Precision: choosing formats under a guaranteed error
   ----------------------------------------------------
   Every op is exact on the reals but two: cast(F, E) rounds E to the format F, and agg(Acc, K:N, E)
   rounds each partial sum to the format Acc (agg(+, ...) sums exactly). The Err of info/4 bounds
   |computed - exact| for every element and every input in its declared range; it is sound: clpBNR
   rounds its bounds outward. A cast that overflows has no bound: info/4 fails.

   7.1 Exact ints. A dot product of int8 values: their products and sums are ints, exact in a
   format while they fit. int16 overflows, bf16 rounds, fp32 holds ints up to 2^24 exactly.

   ?- dot(+, Y), info(Y, K, R, E).
   K = int, R = -4161536-4194304, E = 0.
   ?- dot(int16, Y), info(Y, K, R, E).
   false.
   ?- dot(bf16, Y), info(Y, K, R, E).
   E = 1069547520.0.
   ?- dot(fp32, Y), info(Y, K, R, E).
   E = 0.0.

   choose(Fs, A, Eps) labels the formats Fs, cheapest first, until the bound is at most Eps:

   ?- dot(Acc, Y), choose([Acc], Y, 0).
   Acc = int32.
   ?- z(Z), over([I], cast(int8, Z[I]), A), info(A, K, R, E).
   E = 0.
   ?- z(Z), over([I], cast(int8, Z[I] * 20), A), info(A, K, R, E).
   false.

   7.2 Reals. Each rounding costs half an ulp at the magnitude the range gives; the sum of 64
   rounded products costs its terms' errors and the rounding of each partial sum.

   ?- fdot(fp32, fp32, Y), info(Y, K, R, E).
   K = float, R = -64-64, E = 0.0002479562538190715.
   ?- fdot(fp16, fp32, Y), info(Y, _, _, E).
   E = 0.06277489765408396.
   ?- fdot(bf16, bf16, Y), info(Y, _, _, E).
   E = 21.55699481865285.
   ?- fdot(In, Acc, Y), choose([In, Acc], Y, 0.1).
   In = fp16, Acc = fp32.
   ?- fdot(In, Acc, Y), choose([In, Acc], Y, 1.0e-3).
   In = Acc, Acc = fp32.
   ?- z(Z), over([I], cast(F, Z[I] * 0.1), A), choose([F], A, 1.0e-3).
   F = fp16.

   7.3 Through an op, an error is scaled by the op's derivatives, bounded over the operands'
   ranges widened by their errors (the mean value theorem). A relu written max is 1-Lipschitz;
   written where on data, its rounded condition may flip, which costs the jump between branches.

   ?- z(Z), over([I], exp(cast(bf16, Z[I] * 0.1)), A), info(A, K, R, E).
   R = 1.6487212707001278-2.4596031111569507, E = 0.008677495445102873.
   ?- z(Z), over([I], max(cast(bf16, Z[I] * 0.1) - 0.7, 0), A), info(A, K, R, E).
   E = 0.003515625000000003.
   ?- z(Z), over([I], where(0.7 < cast(bf16, Z[I] * 0.1), Z[I] * 0.1 - 0.7, 0), A), info(A, K, R, E).
   E = 0.2000000000000004.

   A division is bounded when its divisor's range excludes 0, and not otherwise:

   ?- z(Z), over([I], 1 / cast(fp16, Z[I] * 0.5), A), info(A, K, R, E).
   E = 0.0003521860818025262.
   ?- x(X), over([I, J], 1 / cast(fp16, X[I, J] * 0.5), A), info(A, K, R, E).
   R = 0.39999999999999997-1.0Inf, E = 1.0Inf.

   7.4 Casts are lowered as they are, for the kernel to compute in their format; eval/3 runs the
   kernels exactly. A rec that rounds has no bound yet: its range would need a fixpoint.

   ?- z(Z), over([I], cast(fp16, Z[I] * 0.1), A), show(A).
   kernel(out, [5], for(par, A, 5, store(out, A, cast(fp16, load(z, A)*0.1)))).
   ?- z(Z), C = rec(S, [T:5], where(T =:= 0, Z[0] * 0.1, cast(fp16, S[T-1] + Z[T] * 0.1))),
      fold(C, F), info(F, K, R, E).
   false.
*/
