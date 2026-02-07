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
