:- module(grad2_tests, []).

:- use_module(core2).
:- use_module(compile2).
:- use_module(grad2).
:- use_module(opencl, [opencl_device/2]).
:- op(20, yf, []).

% The references are evaluated once for every program and data, then read from the disk:
% see reference.pl.
:- set_prolog_flag(eval_cache, true).

% A derivative is checked against central differences of the reference evaluation: the
% vector-Jacobian product OutBar . dOut/dIn element by element of In, and the Jacobian column
% by column.

vals(N, Seed, Vs) :-
   numlist(1, N, Is),
   maplist(val(Seed), Is, Vs).

val(Seed, I, V) :- V is sin(I*Seed + 0.3).

data_of(N, Data, Xs) :-
   member(M-Xs, Data), M == N, !.

replaced(Data, In, Xs, Data1) :-
   maplist(replace(In, Xs), Data, Data1).

replace(In, Xs, N-V, N-V1) :-
   (  N == In
   -> V1 = Xs
   ;  V1 = V
   ).

bump(Xs, K, H, Ys) :-
   nth1(K, Xs, X, Rest),
   X1 is X + H,
   nth1(K, Ys, X1, Rest).

% column(+Out, +Data, +In, +K, -Col): dOut/dIn[K] by central differences.
column(Out, Data, In, K, Col) :-
   H = 1.0e-6,
   data_of(In, Data, Xs),
   bump(Xs, K, H, Xp), bump(Xs, K, -H, Xm),
   replaced(Data, In, Xp, Dp), replaced(Data, In, Xm, Dm),
   eval(Out, Dp, Yp), eval(Out, Dm, Ym),
   maplist([P, M, D]>>(D is (P - M) / (2*H)), Yp, Ym, Col).

% fd_vjp(+Out, +Data, +In, +Bar, -G): Bar . dOut/dIn.
fd_vjp(Out, Data, In, Bar, G) :-
   data_of(In, Data, Xs), length(Xs, L),
   numlist(1, L, Ks),
   maplist(fd_dot(Out, Data, In, Bar), Ks, G).

fd_dot(Out, Data, In, Bar, K, G) :-
   column(Out, Data, In, K, Col),
   foldl([B, C, S0, S]>>(S is S0 + B*C), Bar, Col, 0.0, G).

near(Xs, Ys) :-
   maplist([X, Y]>>(abs(X - Y) < 1.0e-4 * (1 + abs(Y))), Xs, Ys).

% vjp_matches(+Out, +Data, +Params): the reverse mode of Out agrees with the differences.
vjp_matches(Out, Data, Params) :-
   eval(Out, Data, Ys), length(Ys, NOut), vals(NOut, 0.7, Bar),
   vjp(Out, Params, OutBar, Grads),
   maplist(grad_matches(Out, [OutBar-Bar | Data], Data, Bar), Params, Grads).

grad_matches(Out, GData, Data, Bar, P, G) :-
   eval(G, GData, Gv),
   fd_vjp(Out, Data, P, Bar, Fd),
   near(Gv, Fd).

matmul(A, B, C) :-
   shape(A, [3, 4]), shape(B, [4, 2]),
   over([I:3, J:2], [C[I, J] := 0]),
   over([I:3, J:2, K:4], [C[I, J] := C[I, J] + A[I, K] * B[K, J]]).

softmax(X, Y) :-
   shape(X, [2, 5]),
   over([I:2], [M[I] := -1.0e30]),
   over([I:2, K:5], [M[I] := max(M[I], X[I, K])]),
   over([I:2], [S[I] := 0]),
   over([I:2, K:5], [S[I] := S[I] + exp(X[I, K] - M[I])]),
   over([I:2, J:5], [Y[I, J] := exp(X[I, J] - M[I]) / S[I]]).

recurrence(X, C) :-
   shape(X, [6, 2]),
   over([J:2], [C[0, J] := X[0, J]]),
   over([T:5, J:2], [C[T+1, J] := C[T, J] * 0.9 + X[T+1, J]]).

layer_norm(X, G, Xn) :-
   shape(X, [3, 4]), shape(G, [4]),
   over([I:3], [Mu[I] := 0]),
   over([I:3, J:4], [Mu[I] := Mu[I] + X[I, J]]),
   over([I:3], [Var[I] := 0]),
   over([I:3, K:4], [Var[I] := Var[I] + (X[I, K] - Mu[I] / 4) * (X[I, K] - Mu[I] / 4)]),
   over([I:3, J:4], [Xn[I, J] := (X[I, J] - Mu[I] / 4) / sqrt(Var[I] / 4 + 1.0e-5) * G[J]]).

:- begin_tests(grad2_partials).

test(product, [timeout(10), true(D == B)]) :-
   shape(A, []), shape(B, []),
   grad2:partial(A * B, A, D).
test(quotient, [timeout(10), true(D == -(A / (B * B)))]) :-
   shape(A, []), shape(B, []),
   grad2:partial(A / B, B, D).
test(where_selects, [timeout(10), true(D == where(A < 0, -1, 1))]) :-
   shape(A, []),
   grad2:partial(where(A < 0, -A, A), A, D).
test(subscript_is_constant, [timeout(10), true(D == 1)]) :-
   shape(X, [4]), shape(P, [4]),
   grad2:partial(X[P[0]], X[P[0]], D).

:- end_tests(grad2_partials).

:- begin_tests(grad2_reverse).

test(matmul, [timeout(60)]) :-
   matmul(A, B, C), vals(12, 1.1, Av), vals(8, 1.3, Bv),
   vjp_matches(C, [A-Av, B-Bv], [A, B]).
test(softmax_through_a_max_fold, [timeout(60)]) :-
   softmax(X, Y), vals(10, 0.9, Xv),
   vjp_matches(Y, [X-Xv], [X]).
test(recurrence_runs_backwards, [timeout(60)]) :-
   recurrence(X, C), vals(12, 0.5, Xv),
   vjp_matches(C, [X-Xv], [X]).
test(layer_norm, [timeout(60)]) :-
   layer_norm(X, G, Y), vals(12, 0.4, Xv), vals(4, 2.1, Gv),
   vjp_matches(Y, [X-Xv, G-Gv], [X, G]).

:- end_tests(grad2_reverse).

% jvp_matches(+Outs, +Data, +Ins): the forward mode of Outs along two random directions
% agrees with the differences: dOut[d] = sum over k of dOut/dIn[k] * T[d, k].
jvp_matches(Outs, Data, Ins) :-
   jvp(Outs, Ins, 2, Tangents, OutTs),
   foldl(tangent_data(Data), Ins, Tangents, TData, 1, _),
   append(TData, Data, JData),
   maplist(tangent_matches(Data, JData, Ins, Tangents, TData), Outs, OutTs).

tangent_data(Data, In, T, T-Vs, Seed, Seed1) :-
   data_of(In, Data, Xs), length(Xs, L), N is 2*L,
   vals(N, Seed, Vs), Seed1 is Seed + 0.37.

tangent_matches(Data, JData, Ins, _, TData, Out, OutT) :-
   eval(OutT, JData, Got),
   eval(Out, Data, Ys), length(Ys, NY),
   maplist(directional(Out, Data), Ins, TData, Parts),
   N2 is 2*NY, length(Zero, N2), maplist(=(0.0), Zero),
   foldl([P, A0, A]>>maplist([X, Y, Z]>>(Z is X + Y), P, A0, A), Parts, Zero, Want),
   near(Got, Want).

% directional(+Out, +Data, +In, +T-Vs, -D): the two directional derivatives of Out along the
% rows of Vs, concatenated, by central differences column by column.
directional(Out, Data, In, _-Vs, D) :-
   data_of(In, Data, Xs), length(Xs, L), numlist(1, L, Ks),
   maplist(column(Out, Data, In), Ks, Cols),
   length(V0, L), append(V0, V1, Vs),
   maplist(combine(Cols), [V0, V1], Ds),
   append(Ds, D).

combine(Cols, V, D) :-
   Cols = [C0 | _], length(C0, NY), length(Zero, NY), maplist(=(0.0), Zero),
   foldl([C, W, A0, A]>>maplist({W}/[X, Y, Z]>>(Z is Y + W*X), C, A0, A), Cols, V, Zero, D).

% A batch of constant-velocity tracks observed by range and height: the EKF's transition
% and observation of each state, F[b] = dY[b]/dX[b] and H[b] = dZ[b]/dX[b].
cv_batch(X, Y, Z) :-
   shape(X, [3, 4]), shape(Y, [3, 4]), shape(Z, [3, 2]),
   Xs = [X[B, 0], X[B, 1], X[B, 2], X[B, 3]],
   ukf2:cv_range_model(Xs, [Y0, Y1, Y2, Y3], [Z0, Z1]),
   over([B:3], [Y[B, 0] := Y0, Y[B, 1] := Y1, Y[B, 2] := Y2, Y[B, 3] := Y3,
                Z[B, 0] := Z0, Z[B, 1] := Z1]).

:- use_module(ukf2, []).

:- begin_tests(grad2_forward).

test(matmul, [timeout(60)]) :-
   matmul(A, B, C), vals(12, 1.1, Av), vals(8, 1.3, Bv),
   jvp_matches([C], [A-Av, B-Bv], [A, B]).
test(softmax_through_a_max_fold, [timeout(60)]) :-
   softmax(X, Y), vals(10, 0.9, Xv),
   jvp_matches([Y], [X-Xv], [X]).
test(recurrence, [timeout(60)]) :-
   recurrence(X, C), vals(12, 0.5, Xv),
   jvp_matches([C], [X-Xv], [X]).
test(layer_norm, [timeout(60)]) :-
   layer_norm(X, G, Y), vals(12, 0.4, Xv), vals(4, 2.1, Gv),
   jvp_matches([Y], [X-Xv, G-Gv], [X, G]).
test(ekf_jacobians_of_a_batch, [timeout(60)]) :-
   cv_batch(X, Y, Z),
   jvp([Y, Z], [X], 4, [DX], [F, H]),
   over([D:4, B:3, J:4], [DX[D, B, J] := where(J =:= D, 1.0, 0.0)]),
   Xv = [1.0, 2.0, 0.5, -0.5, 3.0, -4.0, 1.0, 1.0, 0.1, 0.2, 0.0, 2.0],
   eval(F, [X-Xv], Fv), eval(H, [X-Xv], Hv),
   % F[d, b, i] = dY[b, i]/dX[b, d]: the identity and 0.5 on the velocities.
   findall(V, ( between(0, 3, D), between(0, 2, _), between(0, 3, I),
                ( I =:= D -> V = 1.0 ; D =:= I + 2 -> V = 0.5 ; V = 0.0 ) ), Fw),
   near(Fv, Fw),
   % H[d, b, :] = (x, y)/r on the range and (0, 1) on the height, along x and y only.
   findall(V, ( between(0, 3, D), between(0, 2, B), Bx is 4*B, By is Bx + 1,
                nth0(Bx, Xv, Px), nth0(By, Xv, Py), R is sqrt(Px*Px + Py*Py),
                ( D =:= 0 -> member(V, [Px/R, 0.0]) ; D =:= 1 -> member(V, [Py/R, 1.0]) ; member(V, [0.0, 0.0]) ) ), Hw0),
   maplist([E, V]>>(V is E), Hw0, Hw),
   near(Hv, Hw).

:- end_tests(grad2_forward).

% A two-layer MLP with a GELU and a squared-error loss.
mlp_loss(X, T, W1, B1, W2, B2, L, S, D, H) :-
   shape(X, [S, D]), shape(T, [S, D]), shape(W1, [D, H]), shape(B1, [H]), shape(W2, [H, D]), shape(B2, [D]),
   over([I:S, J:H], [C1[I, J] := 0]),
   over([I:S, J:H, K:D], [C1[I, J] := C1[I, J] + X[I, K] * W1[K, J]]),
   over([I:S, J:H], [A[I, J] := (C1[I, J] + B1[J]) * (1 / (1 + exp(-1.702 * (C1[I, J] + B1[J]))))]),
   over([I:S, J:D], [C2[I, J] := 0]),
   over([I:S, J:D, K:H], [C2[I, J] := C2[I, J] + A[I, K] * W2[K, J]]),
   over([I:S, J:D], [Y[I, J] := C2[I, J] + B2[J]]),
   over([], [L := 0]),
   over([I:S, J:D], [L := L + (Y[I, J] - T[I, J]) * (Y[I, J] - T[I, J])]).

mlp_data(S, D, H, X, T, W1, B1, W2, B2, Data) :-
   SD is S*D, DH is D*H,
   vals(SD, 0.11, Xv), vals(SD, 0.13, Tv), vals(DH, 0.017, W1v), vals(H, 0.19, B1v), vals(DH, 0.023, W2v), vals(D, 0.29, B2v),
   Data = [X-Xv, T-Tv, W1-W1v, B1-B1v, W2-W2v, B2-B2v].

% A device's float result against the reference's.
near_device(Xs, Ys) :-
   maplist([X, Y]>>(abs(X - Y) < 1.0e-3 * (1 + abs(Y))), Xs, Ys).

:- begin_tests(grad2_device).

test(mlp_loss_gradients, [timeout(300), forall(opencl_device(D, _))]) :-
   mlp_loss(X, T, W1, B1, W2, B2, L, 64, 32, 128),
   grad(L, [W1, B1, W2, B2], Grads),
   mlp_data(64, 32, 128, X, T, W1, B1, W2, B2, Data),
   forall(member(G, Grads),
          ( eval(G, Data, Ref), run(G, Data, V, [device(D)]), near_device(V, Ref) )).
test(mlp_gradients_agree_with_differences, [timeout(120)]) :-
   mlp_loss(X, T, W1, B1, W2, B2, L, 3, 2, 4),
   mlp_data(3, 2, 4, X, T, W1, B1, W2, B2, Data),
   vjp_matches(L, Data, [W1, B1, W2, B2]).
% One step of gradient descent is a program like any other: the new weights.
test(sgd_step, [timeout(300), forall(opencl_device(D, _))]) :-
   mlp_loss(X, T, W1, B1, W2, B2, L, 64, 32, 128),
   grad(L, [W1, B1, W2, B2], [G1 | _]),
   over([K:32, J:128], [W1n[K, J] := W1[K, J] - 0.01 * G1[K, J]]),
   mlp_data(64, 32, 128, X, T, W1, B1, W2, B2, Data),
   eval(W1n, Data, Ref), run(W1n, Data, V, [device(D)]), near_device(V, Ref).
test(ekf_jacobians, [timeout(120), forall(opencl_device(Dv, _))]) :-
   cv_batch(X, Y, Z),
   jvp([Y, Z], [X], 4, [DX], [F, H]),
   over([D:4, B:3, J:4], [DX[D, B, J] := where(J =:= D, 1.0, 0.0)]),
   vals(12, 0.3, Xv),
   forall(member(Out, [F, H]),
          ( eval(Out, [X-Xv], Ref), run(Out, [X-Xv], V, [device(Dv)]), near_device(V, Ref) )).
% The Cholesky factor of the UKF is updated in place column by column: the values its
% derivative reads are gone when it runs.
test(in_place_cholesky_is_not_available, [timeout(60), throws(error(domain_error(available, _), _))]) :-
   ukf2:ukf_step(ukf2:cv_range_model, dims(2, 4, 2, 3), 9.0, in(Mu, P, R, _, _), out(_, _, _, _, Score, _, _, _)),
   vjp(Score, [Mu, P, R], _, _).

:- end_tests(grad2_device).
