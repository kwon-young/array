:- module(bench_ukf, [go_ukf/1, check_ukf/2, ukf_all/3]).
:- use_module(library(array)).
:- use_module('../examples/ukf').
:- use_module(bench, [bench_data/6]).
:- use_module(library(csv)).

% The UKF step of ukf.pl against bench_ukf.py: the same sizes, and one program computing
% the score, the posterior covariance and the selected mean, pulled by a rank-0 name that
% reads one element of each.

ukf_all(dims(B, N, M, D), in(Mu, P, R, Zdet, Sel), all(Score, PPost, MuSel, All)) :-
   ukf_step(cv_range_model, dims(B, N, M, D), 9.21, in(Mu, P, R, Zdet, Sel), out(_, _, _, _, Score, _, PPost, MuSel)),
   shape(All, []),
   over([], [All := Score[0, 0] + PPost[0, 0, 0] + MuSel[0, 0]]).

sizes([dims(256, 4, 2, 16), dims(4096, 4, 2, 64), dims(65536, 4, 2, 64)]).

% data(+Dims, -Data): means around 10, covariances A A^T / 100 + I / 2, detections around 10.
data(dims(B, N, M, D), [Mu-Mus, P-Ps, R-Rs, Zdet-Zs, Sel-Sels], in(Mu, P, R, Zdet, Sel)) :-
   set_random(seed(0)),
   BN is B*N, length(Mus, BN), maplist([X]>>(X is 10 + 5*random_float), Mus),
   findall(V, ( between(1, B, _), spd(N, Rows), member(Row, Rows), member(V, Row) ), Ps),
   findall(V, ( between(0, M, I), I < M, between(0, M, J), J < M, ( I =:= J -> V = 0.5 ; V = 0 ) ), Rs),
   DM is D*M, length(Zs, DM), maplist([X]>>(X is 10 + 5*random_float), Zs),
   length(Sels, B), maplist({D}/[X]>>(X is random(D)), Sels).

spd(N, S) :-
   findall(Row, ( between(1, N, _), length(Row, N), maplist([X]>>(X is 0.1*random_float), Row) ), A),
   findall(SRow, ( nth1(I, A, Ai), findall(V, ( nth1(J, A, Aj), foldl([X, Y, S0, S1]>>(S1 is S0 + X*Y), Ai, Aj, 0, Dot),
                                                 ( I =:= J -> V is Dot + 0.5 ; V = Dot ) ), SRow) ), S).

go_ukf(Device) :-
   sizes(Sizes),
   forall(member(Dims, Sizes),
          ( data(Dims, Data, In), ukf_all(Dims, In, all(_, _, _, All)),
            Dims = dims(B, N, M, D), format(atom(Lb), "ukf B=~d N=~d M=~d D=~d", [B, N, M, D]),
            bench_data(Lb, All, Data, Device, [], 5) )).

% check_ukf(+Dir, +Device): the outputs on Device against numpy's, dumped by
% bench_ukf.py <Dir> at the first size.
check_ukf(Dir, Device) :-
   maplist(column(Dir), [mu, p, r, z, sel, score, p_post, mu_sel], [Mus, Ps, Rs, Zs, Sels, Score0, PPost0, MuSel0]),
   ukf_all(dims(256, 4, 2, 16), in(Mu, P, R, Zdet, Sel), all(Score, PPost, MuSel, _)),
   Data = [Mu-Mus, P-Ps, R-Rs, Zdet-Zs, Sel-Sels],
   forall(member(Out-Ref-Lb, [Score-Score0-score, PPost-PPost0-p_post, MuSel-MuSel0-mu_sel]),
          ( run(Out, Data, V, [device(Device)]),
            aggregate_all(count, ( nth0(I, Ref, X), nth0(I, V, Y), \+ near(X, Y) ), Bad),
            length(Ref, Len), format("~w ~w: ~d of ~d elements differ from numpy~n", [Device, Lb, Bad, Len]) )).

near(X, Y) :- ( X =:= Y -> true ; abs(X - Y) < 1.0e-3 * (1 + abs(X)) ).

column(Dir, Name, Values) :-
   format(atom(File), "~w/ukf_~w.csv", [Dir, Name]),
   csv_read_file(File, Rows, [convert(true)]),
   maplist([row(X), Y]>>( X == inf -> Y is inf ; Y = X ), Rows, Values).
