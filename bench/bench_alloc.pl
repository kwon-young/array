:- module(bench_alloc, [go_alloc/1, go_alloc/2, example/5]).
:- use_module(library(array)).
:- use_module(library(array/compile)).
:- use_module(bench).
:- use_module('../examples/linalg').
:- use_module('../examples/nn').
:- use_module(bench_ukf, [ukf_all/3]).
:- set_prolog_flag(stack_limit, 4_000_000_000).

% Every example of bench.pl and bench_ukf.pl, run with the intermediates as buffers of their
% own and as slices of one arena, for the memory each takes and the kernel time under each.

example('matmul 512^3', C, Data, [], 5) :- matmul(_, _, C, 512, 512, 512), inputs_data(C, Data).
example('matmul 1024^3', C, Data, [], 3) :- matmul(_, _, C, 1024, 1024, 1024), inputs_data(C, Data).
example('softmax 1024x1024', Y, Data, [local(64)], 5) :- softmax(_, Y, 1024, 1024), inputs_data(Y, Data).
example('softmax 64x4096', Y, Data, [local(128)], 5) :- softmax(_, Y, 64, 4096), inputs_data(Y, Data).
example('dot 1M', S, Data, [local(256)], 5) :- dot(_, _, S, 1048576), inputs_data(S, Data).
example(Label, L, [A-As], [], 3) :-
   member(N, [32, 64, 256, 1024]), cholesky(A, L, N), spd(N, As), format(atom(Label), "cholesky ~d", [N]).
example(Label, L, [A-As], [], 3) :-
   member(M-N, [1024-32, 256-64]), batched_cholesky(A, L, M, N), spd(N, As1),
   findall(X, ( between(1, M, _), member(X, As1) ), As), format(atom(Label), "cholesky ~dx~d batch", [N, M]).
example(Label, L, [A-As], [], 3) :-
   member(N-NB, [256-32, 1024-32, 1024-64]), blocked_cholesky(A, L, N, NB), spd(N, As),
   format(atom(Label), "blocked cholesky ~d nb ~d", [N, NB]).
example(Label, H, [Idx-Is, W-Ws], [], 3) :-
   member(M-N, [1048576-256, 1048576-1048576]), scatter(Idx, W, H, M, N), bench:scatter_data(M, N, Is, Ws),
   format(atom(Label), "scatter ~d into ~d", [M, N]).
example('embedding backward 65536x64 into 10000', E, [Idx-Is, G-Gs], [], 3) :-
   embedding_backward(Idx, G, E, 65536, 10000, 64), bench:scatter_data(65536, 10000, Is, _),
   numlist(1, 4194304, Gs0), maplist([X, Y]>>(Y is X mod 7), Gs0, Gs).
example('mlp 256x768x3072', Y, Data, [], 3) :- mlp(_, Y, 256, 768, 3072), inputs_data(Y, Data).
example('vit block 256x768x12', Y, Data, [], 3) :- vit_block(_, Y, 256, 768, 12, 3072), inputs_data(Y, Data).
example(Label, All, Data, [], 5) :-
   member(Dims, [dims(256, 4, 2, 16), dims(4096, 4, 2, 64), dims(65536, 4, 2, 64)]),
   bench_ukf:data(Dims, Data, In), ukf_all(Dims, In, all(_, _, _, All)),
   Dims = dims(B, N, M, D), format(atom(Label), "ukf B=~d N=~d M=~d D=~d", [B, N, M, D]).

go_alloc(Device) :-
   go_alloc(Device, [separate, arena]).

% go_alloc(+Device, +Hows): a line per example and allocation: the kernels, the best time, the
% bytes of the intermediates, apart and at the peak, and the time to allocate them.
go_alloc(Device, Hows) :-
   format("~w~t~40|~w~t~50|~w~t~60|~w~t~72|~w~t~84|~w~t~96|~w~t~108|~w~n",
          [example, alloc, kernels, 'best ms', 'temps KB', 'apart KB', 'peak KB', 'alloc ms']),
   forall(example(Label, Out, Data, Opts, Reps),
          forall(member(How, Hows),
                 ( bench_stats(Label, Out, Data, Device, [alloc(How) | Opts], Reps, S),
                   stats{kernels: NK, best: Best, bytes: B, apart: Ap, peak: Pk, setup: Setup} :< S,
                   format("~w~t~40|~w~t~50|~d~t~60|~3f~t~72|~d~t~84|~d~t~96|~d~t~108|~3f~n",
                          [Label, How, NK, Best*1000, B // 1024, Ap // 1024, Pk // 1024, Setup*1000]) ))).
