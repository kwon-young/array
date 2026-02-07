:- use_module(library(plunit)).

a(data(0, 5, 22r3,
       4, 2, 1,
       2, 7, 9)).

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
   ;  fmat(A, P, N),
      State = state(0, I),
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
      ValueJ1 is ValueJ rdiv ValueI,
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

lup_solve(A, P, B, N, X) :-
    lup_solve(A, P, B, N, X, 0),
    I1 is N - 1,
    lup_solve_bwd(A, P, N, X, I1).

lup_solve(A, P, B, N, X, I) :-
    (   I == N
    ->  true
    ;   arg0(I, P, PI),
        arg0(PI, B, ValueB),
        nb_setarg0(I, X, ValueB),
        lup_solve(A, P, N, X, I, 0),
        I1 is I + 1,
        lup_solve(A, P, B, N, X, I1)
    ).

lup_solve(A, P, N, X, I, K) :-
    (   K == I
    ->  true
    ;   arg0(I, P, PI),
        Index is PI * N + K,
        arg0(Index, A, ValueA),
        arg0(K, X, ValueK),
        arg0(I, X, ValueI),
        ValueI1 is ValueI - ValueA * ValueK,
        nb_setarg0(I, X, ValueI1),
        K1 is K + 1,
        lup_solve(A, P, N, X, I, K1)
    ).

lup_solve_bwd(A, P, N, X, I) :-
    (   I < 0
    ->  true
    ;   I1 is I + 1,
        lup_solve_bwd(A, P, N, X, I, I1),
        arg0(I, P, PI),
        Index is PI * N + I,
        arg0(Index, A, ValueA),
        arg0(I, X, ValueI),
        ValueI1 is ValueI rdiv ValueA,
        nb_setarg0(I, X, ValueI1),
        I_prev is I - 1,
        lup_solve_bwd(A, P, N, X, I_prev)
    ).

lup_solve_bwd(A, P, N, X, I, K) :-
    (   K == N
    ->  true
    ;   arg0(I, P, PI),
        Index is PI * N + K,
        arg0(Index, A, ValueA),
        arg0(K, X, ValueK),
        arg0(I, X, ValueI),
        ValueI1 is ValueI - ValueA * ValueK,
        nb_setarg0(I, X, ValueI1),
        K1 is K + 1,
        lup_solve_bwd(A, P, N, X, I, K1)
    ).

:- begin_tests(lup).

test(decompose) :-
    a(A_orig),
    copy_term(A_orig, A),
    N = 3,
    lup_decompose(A, N, 0.0001, P),
    A_expected = data(0, 5 rdiv 6, 1 rdiv 4, 4, 2, 1, 1 rdiv 2, 6, 17 rdiv 2),
    P_expected = data(1, 2, 0, 5),
    assertion(A == A_expected),
    assertion(P == P_expected).

test(solve) :-
    a(A_orig),
    B = data(32, 11, 43),
    X_expected = data(1, 2, 3),
    N = 3,
    copy_term(A_orig, A),
    lup_decompose(A, N, 0.0001, P),
    compound_name_arity(X, data, N),
    lup_solve(A, P, B, N, X),
    assertion(approx_equal(X, X_expected, 0.0001)).

approx_equal(T1, T2, Tol) :-
    compound_name_arguments(T1, data, L1),
    compound_name_arguments(T2, data, L2),
    length(L1, N),
    length(L2, N),
    forall(between(1, N, I), (
        nth1(I, L1, V1),
        nth1(I, L2, V2),
        abs(V1 - V2) < Tol
    )).

:- end_tests(lup).
