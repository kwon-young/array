:- module(ir_kernels, [cumsum_kernel/3, trsv_kernel/3, cholesky_kernel/3]).

/** <module> Kernels written in the kernel IR

Kernels whose elements depend on earlier ones, written with iterate/2 and
after/2 (docs/kernel_ir.md), in float64.
*/

% cumsum_kernel(+Rows, +N, -Kernel): the cumulative sum of each row of N,
% in N steps, each reading the previous sum back.
cumsum_kernel(Rows, N, (kernel(O-float64, A-float64) :-
   forall(between(0, R1, R),
          iterate(between(0, N1, K),
                  ( load(A-float64, R*N + K, VA),
                    ( K > 0
                    -> load(after(O-float64, K), R*N + K - 1, P)
                    ;  P = 0.0
                    ),
                    V is P + VA,
                    store(O-float64, R*N + K, V) ))))) :-
   R1 is Rows - 1,
   N1 is N - 1.

% trsv_kernel(+Batch, +N, -Kernel): X solves L X = B, L lower triangular,
% by forward substitution.
trsv_kernel(Batch, N, (kernel(X-float64, L-float64, B-float64) :-
   forall(between(0, B1, P),
          iterate(between(0, N1, I),
                  ( aggregate_all(sum(T),
                       ( between(0, N1, J),
                         ( J < I
                         -> load(L-float64, P*NN + I*N + J, VL),
                            load(after(X-float64, I), P*N + J, VX),
                            T is VL*VX
                         ;  T = 0.0
                         ) ),
                       S),
                    load(B-float64, P*N + I, VB),
                    load(L-float64, P*NN + I*N + I, VD),
                    V is (VB - S)/VD,
                    store(X-float64, P*N + I, V) ))))) :-
   B1 is Batch - 1,
   N1 is N - 1,
   NN is N*N.

% cholesky_kernel(+Batch, +N, -Kernel): L L' = A, L lower triangular, column
% by column, each reading the previous columns back.
cholesky_kernel(Batch, N, (kernel(L-float64, A-float64) :-
   forall(between(0, B1, P),
          iterate(between(0, N1, J),
                  ( aggregate_all(sum(T),
                       ( between(0, N1, K),
                         ( K < J
                         -> load(after(L-float64, J), P*NN + J*N + K, VK),
                            T is VK*VK
                         ;  T = 0.0
                         ) ),
                       S),
                    load(A-float64, P*NN + J*N + J, VA),
                    D is sqrt(VA - S),
                    store(L-float64, P*NN + J*N + J, D),
                    forall(between(0, N1, I),
                           ( I > J
                           -> aggregate_all(sum(U),
                                 ( between(0, N1, K2),
                                   ( K2 < J
                                   -> load(after(L-float64, J), P*NN + I*N + K2, LI),
                                      load(after(L-float64, J), P*NN + J*N + K2, LJ),
                                      U is LI*LJ
                                   ;  U = 0.0
                                   ) ),
                                 S2),
                              load(A-float64, P*NN + I*N + J, VIJ),
                              E is (VIJ - S2)/D,
                              store(L-float64, P*NN + I*N + J, E)
                           ;  I < J
                           -> store(L-float64, P*NN + I*N + J, 0.0)
                           ;  true
                           )) ))))) :-
   B1 is Batch - 1,
   N1 is N - 1,
   NN is N*N.

