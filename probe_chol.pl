:- [bench2].
:- use_module(opencl).

% Where the Cholesky time goes: the plan's ranges, the per-step launches without the update,
% the update alone, and the cost of an empty launch.
chol_no_update(A, L, N) :-
   shape(A, [N, N]), shape(L, [N, N]), shape(C, [N]), shape(D, []),
   over([I:N, J:N], [L[I, J] := where(J =< I, A[I, J], 0)]),
   over([K:N], [over([], [D := sqrt(L[K, K])]),
                over([I:N], [C[I] := where(I =:= K, D, where(K < I, L[I, K] / D, 0))]),
                over([I:N], [L[I, K] := where(K =< I, C[I], L[I, K])])]).
chol_only_update(A, L, N) :-
   shape(A, [N, N]), shape(L, [N, N]), shape(C, [N]),
   over([I:N, J:N], [L[I, J] := where(J =< I, A[I, J], 0)]),
   over([K:N], [over([I:N, J:N], [L[I, J] := where(K < J, where(J =< I, L[I, J] - C[I] * C[J], L[I, J]), L[I, J])])]).

probe(Device, N) :-
   cholesky(_, L, N), compile2:device(Device, Dev, _, _), device_options(Dev, Opts),
   kernels(L, Opts, [_, loop(_, _, Steps)]), last(Steps, U),
   kernel{ranges: R, par: Par} :< U, print(update_ranges(R)-par(Par)), nl,
   spd(N, As),
   cholesky(A1, L1, N), bench_data('cholesky full   ', L1, [A1-As], Device, [], 3),
   chol_no_update(A2, L2, N), bench_data('without update  ', L2, [A2-As], Device, [], 3),
   chol_only_update(A3, L3, N), bench_data('update only     ', L3, [A3-As], Device, [], 3).

empty_launch(Device, Reps) :-
   compile2:device(Device, Dev, Context, Queue),
   cl_program(Context, Dev, "__kernel void k0(__global float *a) { a[0] = 1.0f; }", "", Program),
   cl_kernel(Program, k0, K), cl_buffer(Context, 16, Mem),
   cl_enqueue(Queue, K, [mem(Mem)], 1, 0, [], _), cl_finish(Queue),
   get_time(T0),
   forall(between(1, Reps, _), cl_enqueue(Queue, K, [mem(Mem)], 1, 0, [], _)),
   cl_finish(Queue), get_time(T1),
   Per is (T1 - T0) / Reps * 1.0e6, format("~w: ~1f us per launch~n", [Device, Per]).
