:- use_module('../array.pl').

compute_dog_data(ZVar, ProcessVar, Xs, Zs, Options) :-
   Vel is 0.0,
   ZStd is sqrt(ZVar),
   PStd is sqrt(ProcessVar),
   option(count(Count), Options, 1),
   V @= Vel + array{}.randn([Count]) * PStd,
   option(dt(Dt), Options, 1.0),
   X @= V * Dt,
   Xs = X.cumsum(0),
   Zs @= Xs + array{}.randn([Count]) * ZStd.

predict(F, B, U, Q, X-P, X-P, X_-P_) :-
   X_ @= F@X + B@U,
   P_ @= F@P@F.t() + Q.

update(H, R, Z, X_, P_, X, P) :-
   Y @= Z - H@X_,
   S @= H@P_@H.t()+R,
   HP_ @= H @ P_,
   Kt @= solve(S, HP_),
   K = Kt.t(),
   X @= X_ + K@Y,
   P @= P_ - K @ H @ P_.

q_discrete_white_noise(2, Dt, Var, Q) :-
   Dt4 is Dt^4/4,
   Dt3 is Dt^3/2,
   Dt2 is Dt^2,
   Q @= array{}.fromlist([[Dt4, Dt3], [Dt3, Dt2]]) * Var.

M.pos_vel_filter(X, P, R, Options) := Dict :-
   X.shape() = [2],
   option(dt(Dt), Options, 1.0),
   F = array{}.fromlist([[1.0, Dt], [0.0, 1.0]]),
   H = array{}.fromlist([[1.0, 0.0]]),
   R1 @= X.eye(1, 1, []) * R,
   P1 @= X.eye(2, 2, []) * P,
   option(q(Q), Options, 0.0),
   (  number(Q)
   -> q_discrete_white_noise(2, Dt, Q, Q1)
   ;  Q.shape() = [2, 2], Q1 = Q
   ),
   Dict = M.put([x=X, f=F, h=H, r=R1.realize(), p=P1.realize(), q=Q1.realize()]).

:- begin_tests(kalman).

test('state initialization') :-
   _X = array{}.fromlist([10.0, 4.5]).

test('dot') :-
   A = array{}.fromlist([[1, 2], [3, 4]]),
   X = array{}.fromlist([[10.0], [4.5]]),
   R @= A @ X,
   [[19.0], [48.0]] = R.tolist().

test('state covariance') :-
   P = array{}.fromlist([500.0, 49.0]).diag(),
   P.tolist() = [[500.0, 0], [0, 49.0]].

test('state transition matrix') :-
   Dt = 0.1,
   _F = array{}.fromlist([[1, Dt], [0, 1]]).

test('predict') :-
   X = array{}.fromlist([10.0, 4.5]),
   P = array{}.fromlist([500.0, 49.0]).diag(),
   Dt = 0.1,
   F = array{}.fromlist([[1, Dt], [0, 1]]),
   B = array{}.zeros([2, 2]),
   U = array{}.zeros([2]),
   length(State, 5),
   foldl(predict(F, B, U, 0), State, X-P, X_-P_),
   X_.tolist() = [12.249999999999996, 4.5],
   P_.tolist() = [[512.2500000000001, 24.5], [24.5, 49.0]].

test('Q discrete white noise') :-
   _Q = array{}.fromlist([[0.588, 1.175], [1.175, 2.35 ]]).

test('H') :-
   _H = array{}.fromlist([[1.0, 0.0]]).

test('R') :-
   _R = array{}.fromlist([[5.0]]).

test('update') :-
   X_ = array{}.fromlist([10.0, 4.5]),
   P_ = array{}.fromlist([500.0, 49.0]).diag(),
   R = array{}.fromlist([[5.0]]),
   H = array{}.fromlist([[1.0, 0.0]]),
   update(H, R, 1.0, X_, P_, X, P),
   X.tolist() = X1,
   P.tolist() = P1.

:- end_tests(kalman).
