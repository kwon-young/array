:- use_module(core2).
:- use_module(compile2).
:- use_module(ukf2).
:- use_module(opencl, [opencl_device/2]).
:- use_module(library(clpfd), [transpose/2]).

% The references are evaluated once for every program and data, then read from the disk:
% see reference.pl.
:- set_prolog_flag(eval_cache, true).

% The step is checked against a reference on lists: the same model run with is/2 at the
% sigma points, the moments by hand, and, the observation being 2-dimensional, the closed
% forms of the inverse and the determinant of Szz. The reference runs on one state; the
% batch is the states one after the other.

near(Xs, Ys) :-
   maplist([X, Y]>>( X =:= Y -> true ; abs(X - Y) < 1.0e-3 * (1 + abs(X)) ), Xs, Ys).

% A list Cholesky, row by row (Cholesky-Banachiewicz).
chol_ref(A, L) :-
   foldl(chol_row, A, L, [], _).

chol_row(ARow, LRow, Done, Done1) :-
   foldl(chol_elem(ARow), Done, [], Pre),
   length(Pre, I), nth0(I, ARow, Aii), dot_prefix(Pre, Pre, S), Lii is sqrt(Aii - S),
   length(ARow, N), Z is N - I - 1, length(Zeros, Z), maplist(=(0.0), Zeros),
   append([Pre, [Lii], Zeros], LRow), append(Done, [LRow], Done1).

chol_elem(ARow, LRowJ, Acc0, Acc) :-
   length(Acc0, J), nth0(J, ARow, Aij), nth0(J, LRowJ, Ljj),
   dot_prefix(Acc0, LRowJ, S),
   Lij is (Aij - S) / Ljj, append(Acc0, [Lij], Acc).

dot_prefix(Xs, Ys, S) :-
   same_length(Xs, Pre), append(Pre, _, Ys),
   foldl([X, Y, S0, S1]>>(S1 is S0 + X*Y), Xs, Pre, 0.0, S).

vec_add(X, Y, Z) :- maplist([A, B, C]>>(C is A + B), X, Y, Z).
vec_sub(X, Y, Z) :- maplist([A, B, C]>>(C is A - B), X, Y, Z).
vec_dot(X, Y, D) :- foldl([A, B, S0, S]>>(S is S0 + A*B), X, Y, 0.0, D).
mat_vec(M, V, R) :- maplist([Row, X]>>vec_dot(Row, V, X), M, R).
mat_mul(A, B, C) :- transpose(B, Bt), maplist([Row, CRow]>>mat_vec(Bt, Row, CRow), A, C).
mat_sub(A, B, C) :- maplist(vec_sub, A, B, C).
mat_scale(S, A, B) :- maplist([Row, Row1]>>maplist([X, Y]>>(Y is S*X), Row, Row1), A, B).
mean(Rows, Mu) :- length(Rows, K), transpose(Rows, Cols), maplist([Col, M]>>(sum_list(Col, S), M is S / K), Cols, Mu).

% cov(+As, +Bs, -C): the K rows of As and Bs are paired samples, C their covariance with
% weights 1/K.
cov(As, Bs, C) :-
   mean(As, MA), mean(Bs, MB), length(As, K),
   maplist({MA}/[A, D]>>vec_sub(A, MA, D), As, DAs),
   maplist({MB}/[B, D]>>vec_sub(B, MB, D), Bs, DBs),
   transpose(DAs, DAt), transpose(DBs, DBt),
   maplist({DBt, K}/[Ai, Row]>>maplist({Ai, K}/[Bj, X]>>(vec_dot(Ai, Bj, S), X is S / K), DBt, Row), DAt, C).

inv2([[A, B], [C, D]], [[IA, IB], [IC, ID]]) :-
   Det is A*D - B*C, IA is D/Det, IB is -B/Det, IC is -C/Det, ID is A/Det.
logdet2([[A, B], [C, D]], L) :- L is log(A*D - B*C).

% ukf_ref(+Model, +Crit, +Mu, +P, +R, +Zdets, +Sel, -Out): one state against every detection.
ukf_ref(Model, Crit, Mu, P, R, Zdets, Sel, out(MuPred, PPred, MuZ, Szz, Scores, MuPosts, PPost, MuSel)) :-
   length(Mu, N), K is 2*N, length(Zdets, D),
   mat_scale(N, P, S), chol_ref(S, L), transpose(L, Cols),
   maplist({Mu}/[Col, X]>>vec_add(Mu, Col, X), Cols, Plus),
   maplist({Mu}/[Col, X]>>vec_sub(Mu, Col, X), Cols, Minus),
   append(Plus, Minus, Xs), length(Xs, K),
   maplist({Model}/[X, Y, Z]>>( call(Model, X, YE, ZE), maplist([E, V]>>(V is E), YE, Y), maplist([E, V]>>(V is E), ZE, Z) ),
           Xs, Ys, Zs),
   mean(Ys, MuPred), mean(Zs, MuZ),
   cov(Ys, Ys, PPred), cov(Zs, Zs, Czz), cov(Ys, Zs, Pyz),
   maplist(vec_add, Czz, R, Szz),
   inv2(Szz, Sinv), logdet2(Szz, LogDet), length(MuZ, M), C0 is 0.5*M*log(2*pi),
   maplist({MuZ}/[Zd, E]>>vec_sub(Zd, MuZ, E), Zdets, Es),
   maplist({Sinv, LogDet, C0, Crit}/[E, Sc]>>( mat_vec(Sinv, E, SE), vec_dot(E, SE, D2),
                                                ( D2 =< Crit -> Sc is 0.5*D2 + 0.5*LogDet + C0 ; Sc is inf ) ),
           Es, Scores),
   mat_mul(Pyz, Sinv, G),
   maplist({G, MuPred}/[E, MuPost]>>( mat_vec(G, E, GE), vec_add(MuPred, GE, MuPost) ), Es, MuPosts),
   mat_mul(G, Szz, GS), transpose(G, Gt), mat_mul(GS, Gt, GSGt), mat_sub(PPred, GSGt, PPost),
   length(MuPosts, D), nth0(Sel, MuPosts, MuSel).

% Two tracks, four-dimensional, two detections near their predicted observations and one
% far away.
case(dims(2, 4, 2, 3), 9.21, [Mu-MuL, P-PL, R-RL, Zdet-ZL, Sel-SelL], in(Mu, P, R, Zdet, Sel), Ref) :-
   Mus = [[10, 5, 1, 0.5], [3, 8, -1, 0.2]],
   Ps = [[[1, 0.2, 0, 0], [0.2, 1, 0, 0], [0, 0, 0.5, 0.1], [0, 0, 0.1, 0.5]],
         [[0.8, 0, 0.1, 0], [0, 1.2, 0, 0.1], [0.1, 0, 0.4, 0], [0, 0.1, 0, 0.3]]],
   Rs = [[0.5, 0.1], [0.1, 0.5]],
   Zdets = [[11.5, 5.3], [8.4, 8.0], [30, 30]],
   Sels = [0, 1],
   maplist({Rs, Zdets}/[M1, P1, S1, O]>>ukf_ref(cv_range_model, 9.21, M1, P1, Rs, Zdets, S1, O), Mus, Ps, Sels, Ref),
   flatten(Mus, MuL), flatten(Ps, PL), flatten(Rs, RL), flatten(Zdets, ZL), SelL = Sels.

% expected(+Field, +Refs, -Flat): the field of every state's reference, flattened in order.
expected(Field, Refs, Flat) :-
   maplist({Field}/[Ref, V]>>arg(Field, Ref, V), Refs, Vs), flatten(Vs, Flat).

fields([1-mu_pred, 2-p_pred, 3-mu_z, 4-szz, 5-score, 6-mu_post, 7-p_post, 8-mu_sel]).

% more_detections(+Zdet, +Pair, -Pair1): the data of Zdet with two detections appended, the
% near one of the second track and the far one again.
more_detections(Zdet, N-L, N-L1) :-
   (  N == Zdet
   -> append(L, [8.4, 8.0, 30, 30], L1)
   ;  L1 = L
   ).

:- begin_tests(ukf2).

test(eval_matches_reference, [timeout(60), forall((fields(Fs), member(I-Name, Fs)))]) :-
   case(Dims, Crit, Data, In, Refs),
   ukf_step(cv_range_model, Dims, Crit, In, Out),
   arg(I, Out, Name1), expected(I, Refs, Expected),
   eval(Name1, Data, V),
   (  near(Expected, V)
   -> true
   ;  format("~w~n expected ~w~n got      ~w~n", [Name, Expected, V]), fail
   ).

test(run_matches_reference, [timeout(300), forall((opencl_device(D, _), member(I-Name, [5-score, 7-p_post, 8-mu_sel])))]) :-
   case(Dims, Crit, Data, In, Refs),
   ukf_step(cv_range_model, Dims, Crit, In, Out),
   arg(I, Out, Name1), expected(I, Refs, Expected),
   run(Name1, Data, V, [device(D)]),
   (  near(Expected, V)
   -> true
   ;  format("~w ~w~n expected ~w~n got      ~w~n", [D, Name, Expected, V]), fail
   ).

% The far detection is outside the gate of both states, the near ones inside their own.
test(gate, [timeout(60), true(Open == [1, 0, 0, 0, 1, 0])]) :-
   case(Dims, Crit, Data, In, _),
   ukf_step(cv_range_model, Dims, Crit, In, out(_, _, _, _, Score, _, _, _)),
   eval(Score, Data, V),
   maplist([S, O]>>( S =:= inf -> O = 0 ; O = 1 ), V, Open).

% The selected posterior mean is the row of the pair update at the chosen detection.
test(selection_gathers_the_pair, [timeout(60)]) :-
   case(Dims, Crit, Data, In, _),
   ukf_step(cv_range_model, Dims, Crit, In, out(_, _, _, _, _, MuPost, _, MuSel)),
   eval(MuPost, Data, Pairs), eval(MuSel, Data, Sel),
   length(Row0, 4), length(Skip, 4), length(Row1, 4),
   append([Row0, _, _, Skip, Row1, _], Pairs), append(Row0, Row1, Sel).

% The batch and the detections are extent variables until the data fixes them: the step
% is built once for the model, before the sizes are known.
test(symbolic_batch_and_detections, [timeout(60)]) :-
   case(dims(B0, N, M, D0), Crit, Data, in(Mu, P, R, Zdet, Sel), Refs),
   ukf_step(cv_range_model, dims(B, N, M, D), Crit, in(Mu, P, R, Zdet, Sel), Out),
   \+ ground(B-D),
   B = B0, D = D0,
   forall(member(I, [5, 7, 8]),
          ( arg(I, Out, Name), expected(I, Refs, Expected), eval(Name, Data, V), near(Expected, V) )).

% One step for every number of detections: built with D unknown, run at three and at five.
test(one_step_for_every_detection_count, [timeout(300), forall(opencl_device(D, _))]) :-
   case(dims(B0, N, M, _), Crit, Data3, in(Mu, P, R, Zdet, Sel), Refs),
   ukf_step(cv_range_model, dims(B, N, M, Dn), Crit, in(Mu, P, R, Zdet, Sel), Out),
   arg(5, Out, Score),
   expected(5, Refs, Expected3), run(Score, Data3, V3, [device(D)]), near(Expected3, V3),
   maplist(more_detections(Zdet), Data3, Data5),
   eval(Score, Data5, Ref5), run(Score, Data5, V5, [device(D)]), near(Ref5, V5),
   length(V3, L3), length(V5, L5), L3 =:= B0*3, L5 =:= B0*5,
   var(B), var(Dn).

% The step compiles to a bounded number of kernels per output.
test(kernel_count, [timeout(60), true(Ns == [13, 15, 15])]) :-
   case(Dims, Crit, _, In, _),
   ukf_step(cv_range_model, Dims, Crit, In, out(_, _, _, _, Score, _, PPost, MuSel)),
   maplist([Out, N]>>( kernels(Out, [], Plan), compile2:flat_plan(Plan, Flat), length(Flat, N) ), [Score, PPost, MuSel], Ns).

:- end_tests(ukf2).
