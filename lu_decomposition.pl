:- module(lu_decomposition, [solve/5, solve/8]).

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

lup_solve(A, P, B, OB, N, M, X, OX) :-
    lup_solve(A, P, B, OB, N, M, X, OX, 0).

lup_solve(A, P, B, OB, N, M, X, OX, Col) :-
    (   Col == M
    ->  true
    ;   lup_solve_col_fwd(A, P, B, OB, N, M, Col, X, OX, 0),
        I1 is N - 1,
        lup_solve_col_bwd(A, P, N, M, Col, X, OX, I1),
        Col1 is Col + 1,
        lup_solve(A, P, B, OB, N, M, X, OX, Col1)
    ).

lup_solve_col_fwd(A, P, B, OB, N, M, Col, X, OX, I) :-
    (   I == N
    ->  true
    ;   arg0(I, P, PI),
        B_Index is OB + PI * M + Col,
        arg0(B_Index, B, ValueB),
        X_Index is OX + I * M + Col,
        nb_setarg0(X_Index, X, ValueB),
        lup_solve_col_fwd_(A, P, N, M, Col, X, OX, I, 0),
        I1 is I + 1,
        lup_solve_col_fwd(A, P, B, OB, N, M, Col, X, OX, I1)
    ).

lup_solve_col_fwd_(A, P, N, M, Col, X, OX, I, K) :-
    (   K == I
    ->  true
    ;   arg0(I, P, PI),
        A_Index is PI * N + K,
        arg0(A_Index, A, ValueA),
        XK_Index is OX + K * M + Col,
        arg0(XK_Index, X, ValueK),
        XI_Index is OX + I * M + Col,
        arg0(XI_Index, X, ValueI),
        ValueI1 is ValueI - ValueA * ValueK,
        nb_setarg0(XI_Index, X, ValueI1),
        K1 is K + 1,
        lup_solve_col_fwd_(A, P, N, M, Col, X, OX, I, K1)
    ).

lup_solve_col_bwd(A, P, N, M, Col, X, OX, I) :-
    (   I < 0
    ->  true
    ;   I1 is I + 1,
        lup_solve_col_bwd_(A, P, N, M, Col, X, OX, I, I1),
        arg0(I, P, PI),
        A_Index is PI * N + I,
        arg0(A_Index, A, ValueA),
        XI_Index is OX + I * M + Col,
        arg0(XI_Index, X, ValueI),
        ValueI1 is ValueI / ValueA,
        nb_setarg0(XI_Index, X, ValueI1),
        I_prev is I - 1,
        lup_solve_col_bwd(A, P, N, M, Col, X, OX, I_prev)
    ).

lup_solve_col_bwd_(A, P, N, M, Col, X, OX, I, K) :-
    (   K == N
    ->  true
    ;   arg0(I, P, PI),
        A_Index is PI * N + K,
        arg0(A_Index, A, ValueA),
        XK_Index is OX + K * M + Col,
        arg0(XK_Index, X, ValueK),
        XI_Index is OX + I * M + Col,
        arg0(XI_Index, X, ValueI),
        ValueI1 is ValueI - ValueA * ValueK,
        nb_setarg0(XI_Index, X, ValueI1),
        K1 is K + 1,
        lup_solve_col_bwd_(A, P, N, M, Col, X, OX, I, K1)
    ).

%!  solve(+A:data, +B:data, +N:integer, +M:integer, -X:data) is semidet.
%
%  Solve A.X = B for X.  A and B are dedicated data buffers.  If X is
%  unbound, it is created as a fresh data/(N*M) compound.
solve(A, B, N, M, X) :-
   Size is N * M,
   compound_name_arity(X, data, Size),
   solve(A, 0, B, 0, N, M, X, 0).

%!  solve(+A:data, +OffsetA:integer, +B:data, +OffsetB:integer,
%!        +N:integer, +M:integer, +X:data, +OffsetX:integer) is semidet.
%
%  Offset-aware entry point used by the device runtimes.  A, B and X
%  may be shared device buffers: the matrix of A starts at element
%  OffsetA, the matrix of B at OffsetB and the solution is written at
%  OffsetX.  The matrix A is factorized on a private copy, so neither
%  A nor B is modified in place.
solve(A, OffsetA, B, OffsetB, N, M, X, OffsetX) :-
   debug(solve, "A ~p", [A]),
   debug(solve, "B ~p", [B]),
   debug(solve, "N-M ~p", [N-M]),
   Tol = 1e-12,
   copy_matrix(A, OffsetA, N, A1),
   lup_decompose(A1, N, Tol, P),
   lup_solve(A1, P, B, OffsetB, N, M, X, OffsetX).

%!  copy_matrix(+A:data, +Offset:integer, +N:integer, -A1:data) is det.
%
%  Copy the N*N matrix stored at element Offset of buffer A into a
%  fresh data/(N*N) compound.  The LU decomposition works in place on
%  the copy, leaving the original buffer untouched.
copy_matrix(A, Offset, N, A1) :-
   Size is N * N,
   copy_matrix_(A, Offset, Size, 0, Values),
   compound_name_arguments(A1, data, Values).

copy_matrix_(_, _, Size, I, []) :-
   I == Size, !.
copy_matrix_(A, Offset, Size, I, [Value | Values]) :-
   I1 is Offset + I,
   arg0(I1, A, Value),
   I2 is I + 1,
   copy_matrix_(A, Offset, Size, I2, Values).
   
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

fill(_, _, []).
fill(T, Offset, [V | Vs]) :-
    nb_setarg0(Offset, T, V),
    Offset1 is Offset + 1,
    fill(T, Offset1, Vs).

test(solve_shared_offsets) :-
    N = 3,
    M = 1,
    OA = 2,
    OB = 12,
    OX = 16,
    compound_name_arity(Shared, data, 20),
    fill(Shared, 0, [0, 0,
                     0, 5, 22r3,
                     4, 2, 1,
                     2, 7, 9,
                     0,
                     32, 11, 43,
                     0,
                     0, 0, 0,
                     0]),
    solve(Shared, OA, Shared, OB, N, M, Shared, OX),
    X_Expected = data(1.0000000000000049, 1.9999999999999847, 3.0000000000000107),
    forall(between(0, 2, I),
           (  arg0(OX + I, Shared, V),
              arg0(I, X_Expected, VE),
              assertion(V == VE)
           )),
    a(A0),
    B0 = data(32, 11, 43),
    forall(between(0, 8, I),
           (  arg0(OA + I, Shared, VA),
              arg0(I, A0, VE),
              assertion(VA == VE)
           )),
    forall(between(0, 2, I),
           (  arg0(OB + I, Shared, VB),
              arg0(I, B0, VE),
              assertion(VB == VE)
           )).

:- end_tests(lup).
