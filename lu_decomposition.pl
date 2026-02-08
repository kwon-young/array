:- module(lu_decomposition, [solve/5]).

arg0(I, T, V) :-
   I1 is I + 1,
   arg(I1, T, V).
nb_setarg0(I, T, V) :-
   I1 is I + 1,
   nb_setarg(I1, T, V).

lup_decompose(A, N, Tol, P) :-
   numlist(0, N, PArgs),
   compound_name_arguments(P, data, PArgs),
   lup_decompose(A, N, Tol, P, 0).
max(A, P, N, I, State, K) :-
   (  K == N
   -> true
   ;  arg0(K, P, PK),
      Index is PK*N+I,
      arg0(Index, A, Value),
      AbsA is abs(Value),
      arg0(0, State, MaxA),
      (  AbsA > MaxA
      -> nb_setarg0(0, State, AbsA),
         nb_setarg0(1, State, K)
      ;  true
      ),
      K1 is K+1,
      max(A, P, N, I, State, K1)
   ).

lup_decompose(A, N, Tol, P, I) :-
   (  I == N
   -> true
   ;  State = state(0, I),
      max(A, P, N, I, State, I),
      State = state(MaxA, IMax),
      MaxA >= Tol,
      (  IMax =\= I
      -> arg0(I, P, J),
         arg0(IMax, P, PI),
         nb_setarg0(I, P, PI),
         nb_setarg0(IMax, P, J),
         arg0(N, P, PN),
         PN1 is PN + 1,
         nb_setarg0(N, P, PN1)
      ;  true
      ),
      I1 is I + 1,
      lup_decompose(A, N, Tol, P, I, I1),
      lup_decompose(A, N, Tol, P, I1)
   ).

lup_decompose(A, N, Tol, P, I, J) :-
   (  J == N
   -> true
   ;  arg0(J, P, PJ),
      arg0(I, P, PI),
      IndexJ is PJ*N+I,
      IndexI is PI*N+I,
      arg0(IndexJ, A, ValueJ),
      arg0(IndexI, A, ValueI),
      ValueJ1 is ValueJ / ValueI,
      nb_setarg0(IndexJ, A, ValueJ1),
      I1 is I + 1,
      lup_decompose(A, N, Tol, P, I, J, I1),
      J1 is J + 1,
      lup_decompose(A, N, Tol, P, I, J1)
   ).

lup_decompose(A, N, Tol, P, I, J, K) :-
   (  K == N
   -> true
   ;  arg0(J, P, PJ),
      IndexJK is PJ*N + K,
      arg0(IndexJK, A, ValueJK),
      IndexJI is PJ*N + I,
      arg0(IndexJI, A, ValueJI),
      arg0(I, P, PI),
      IndexIK is PI*N + K,
      arg0(IndexIK, A, ValueIK),
      ValueJK1 is ValueJK - ValueJI*ValueIK,
      nb_setarg0(IndexJK, A, ValueJK1),
      K1 is K + 1,
      lup_decompose(A, N, Tol, P, I, J, K1)
   ).

fmat(A, P, N) :-
   fmat(A, P, N, 0), nl.
fmat(A, P, N, I) :-
   (  I == N
   -> true
   ;  arg0(I, P, PI),
      Offset is PI*N,
      fmat_row(A, N, Offset, 0), nl,
      I1 is I+1,
      fmat(A, P, N, I1)
   ).
fmat_row(A, N, Offset, J) :-
   (  J == N
   -> true
   ;  Index is Offset + J,
      arg0(Index, A, Value),
      format("~t~p   ", [Value]),
      J1 is J + 1,
      fmat_row(A, N, Offset, J1)
   ).

lup_solve(A, P, B, N, M, X) :-
    Size is N * M,
    compound_name_arity(X, data, Size),
    lup_solve(A, P, B, N, M, X, 0).

lup_solve(A, P, B, N, M, X, Col) :-
    (   Col == M
    ->  true
    ;   lup_solve_col_fwd(A, P, B, N, M, Col, X, 0),
        I1 is N - 1,
        lup_solve_col_bwd(A, P, N, M, Col, X, I1),
        Col1 is Col + 1,
        lup_solve(A, P, B, N, M, X, Col1)
    ).

lup_solve_col_fwd(A, P, B, N, M, Col, X, I) :-
    (   I == N
    ->  true
    ;   arg0(I, P, PI),
        B_Index is PI * M + Col,
        arg0(B_Index, B, ValueB),
        X_Index is I * M + Col,
        nb_setarg0(X_Index, X, ValueB),
        lup_solve_col_fwd_(A, P, N, M, Col, X, I, 0),
        I1 is I + 1,
        lup_solve_col_fwd(A, P, B, N, M, Col, X, I1)
    ).

lup_solve_col_fwd_(A, P, N, M, Col, X, I, K) :-
    (   K == I
    ->  true
    ;   arg0(I, P, PI),
        A_Index is PI * N + K,
        arg0(A_Index, A, ValueA),
        XK_Index is K * M + Col,
        arg0(XK_Index, X, ValueK),
        XI_Index is I * M + Col,
        arg0(XI_Index, X, ValueI),
        ValueI1 is ValueI - ValueA * ValueK,
        nb_setarg0(XI_Index, X, ValueI1),
        K1 is K + 1,
        lup_solve_col_fwd_(A, P, N, M, Col, X, I, K1)
    ).

lup_solve_col_bwd(A, P, N, M, Col, X, I) :-
    (   I < 0
    ->  true
    ;   I1 is I + 1,
        lup_solve_col_bwd_(A, P, N, M, Col, X, I, I1),
        arg0(I, P, PI),
        A_Index is PI * N + I,
        arg0(A_Index, A, ValueA),
        XI_Index is I * M + Col,
        arg0(XI_Index, X, ValueI),
        ValueI1 is ValueI / ValueA,
        nb_setarg0(XI_Index, X, ValueI1),
        I_prev is I - 1,
        lup_solve_col_bwd(A, P, N, M, Col, X, I_prev)
    ).

lup_solve_col_bwd_(A, P, N, M, Col, X, I, K) :-
    (   K == N
    ->  true
    ;   arg0(I, P, PI),
        A_Index is PI * N + K,
        arg0(A_Index, A, ValueA),
        XK_Index is K * M + Col,
        arg0(XK_Index, X, ValueK),
        XI_Index is I * M + Col,
        arg0(XI_Index, X, ValueI),
        ValueI1 is ValueI - ValueA * ValueK,
        nb_setarg0(XI_Index, X, ValueI1),
        K1 is K + 1,
        lup_solve_col_bwd_(A, P, N, M, Col, X, I, K1)
    ).

solve(A, B, N, M, X) :-
   debug(solve, "A ~p", [A]),
   debug(solve, "B ~p", [B]),
   debug(solve, "N-M ~p", [N-M]),
   Tol = 1e-12,
   lup_decompose(A, N, Tol, P),
   lup_solve(A, P, B, N, M, X).
   
:- begin_tests(lup).

a(data(0, 5, 22r3,
       4, 2, 1,
       2, 7, 9)).

% test(decompose) :-
%     a(A),
%     N = 3,
%     lup_decompose(A, N, 1e-12, P),
%     A_expected = data(0, 5r6, 1r4, 4, 2, 1, 1r2, 6, 17r2),
%     P_expected = data(1, 2, 0, 5),
%     assertion(A == A_expected),
%     assertion(P == P_expected).

test(solve) :-
    a(A),
    B = data(32, 11, 43),
    N = 3,
    solve(A, B, N, 1, X),
    X == data(1.0000000000000049, 1.9999999999999847, 3.0000000000000107).

:- end_tests(lup).
