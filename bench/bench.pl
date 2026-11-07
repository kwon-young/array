:- module(bench, [go/1, go/2, go_chol/1, go_blocked/1, go_scatter/1, go_mlp/1, go_vit/1,
                  bench/6, bench_data/6, bench_stats/7, once_run/4, once_run/5, data/2, inputs_data/2]).
:- use_module(library(array)).
:- use_module(library(array/opencl), [cl_finish/1]).
:- use_module('../examples/linalg').
:- use_module('../examples/nn').
:- set_prolog_flag(stack_limit, 4_000_000_000).

% Kernel time alone: the program is built and the buffers uploaded before the clock starts; a
% run is every kernel launched in order and the queue drained. The best of Reps is reported.

go_chol(Device) :-
   forall(member(N, [32, 64, 256, 1024]),
          ( cholesky(A, L, N), spd(N, As), format(atom(Lb), "cholesky ~d", [N]),
            bench_data(Lb, L, [A-As], Device, [], 3) )),
   forall(member(M-N, [1024-32, 256-64]),
          ( batched_cholesky(A, L, M, N), spd(N, As1), findall(X, ( between(1, M, _), member(X, As1) ), As),
            format(atom(Lb), "cholesky ~dx~d batch", [N, M]),
            bench_data(Lb, L, [A-As], Device, [], 3) )).

go_blocked(Device) :-
   forall(member(N-NB, [256-32, 1024-32, 1024-64]),
          ( blocked_cholesky(A, L, N, NB), spd(N, As), format(atom(Lb), "blocked cholesky ~d nb ~d", [N, NB]),
            bench_data(Lb, L, [A-As], Device, [], 3) )).

% bench_data(+Label, +Out, +Data, +Device, +Options, +Reps): the best kernel time of Reps runs,
% and the memory of the intermediates: the bytes they take, under alloc(arena) the arena, as
% separate buffers apart, the peak live at one kernel, and the time to allocate them.
bench_data(Label, Out, Data, Device, Options0, Reps) :-
   bench_stats(Label, Out, Data, Device, Options0, Reps, S),
   stats{kernels: NK, best: Best, alloc: How, bytes: B, apart: Ap, peak: Pk, setup: Setup} :< S,
   format("~w  ~w  kernels=~d  best=~3f ms  ~w: ~d KB (apart ~d KB, peak ~d KB) in ~3f ms~n",
          [Label, Device, NK, Best*1000, How, B // 1024, Ap // 1024, Pk // 1024, Setup*1000]).

% bench_stats(+Label, +Out, +Data, +Device, +Options, +Reps, -Stats): the figures bench_data/6
% prints, as a dict.
bench_stats(Label, Out, Data, Device, Options0, Reps, Stats) :-
   compile:device(Device, Dev, Context, Queue),
   device_options(Dev, Derived),
   merge_options(Options0, Derived, Options),
   compile:kernels(Out, Options, Kernels),
   compile:source(Kernels, Source),
   compile:built(Context, Dev, Source, Program),
   compile:flat_plan(Kernels, Flat), length(Flat, NK),
   findall(Stats0,                                       % the extents bound by the data, as run/4 does
           ( compile:bind_extents(Kernels, Data),
             compile:allocate(Context, Queue, Dev, Kernels, Out, Data, Options, Alloc),
             alloc{how: How, buffers: Buffers, bytes: B, apart: Ap, peak: Pk, setup: Setup} :< Alloc,
             once_run(Queue, Program, Buffers, Kernels),           % warm up
             findall(T, ( between(1, Reps, _), once_run(Queue, Program, Buffers, Kernels, T) ), Ts),
             min_list(Ts, Best),
             Stats0 = stats{label: Label, device: Device, kernels: NK, best: Best, alloc: How, bytes: B, apart: Ap,
                            peak: Pk, setup: Setup} ),
           [Stats]).

scatter_data(M, N, Is, Ws) :-
   numlist(1, M, Ks), maplist([X, Y]>>(Y is (X * 7919) mod N), Ks, Is), maplist([X, Y]>>(Y is X mod 97), Ks, Ws).

go_scatter(Device) :-
   forall(member(M-N, [1048576-256, 1048576-1048576]),
          ( scatter(Idx, W, H, M, N), scatter_data(M, N, Is, Ws), format(atom(Lb), "scatter ~d into ~d", [M, N]),
            bench_data(Lb, H, [Idx-Is, W-Ws], Device, [], 3) )),
   embedding_backward(Idx2, G, E, 65536, 10000, 64), scatter_data(65536, 10000, Is2, _),
   numlist(1, 4194304, Gs0), maplist([X, Y]>>(Y is X mod 7), Gs0, Gs),
   bench_data('embedding backward 65536x64 into 10000', E, [Idx2-Is2, G-Gs], Device, [], 3).

go_vit(Device) :-
   S = 256, D = 768, H = 12, F = 3072,
   vit_block(X, Y, S, D, H, F),
   inputs_data(Y, Data),
   bench_data(vit_block_256x768x12, Y, Data, Device, [], 3), shape(X, _).

go_mlp(Device) :-
   S = 256, D = 768, H = 3072,
   mlp(X, Y, S, D, H),
   inputs_data(Y, Data),
   bench_data(mlp_256x768x3072, Y, Data, Device, [], 3), shape(X, _).

% inputs_data(+Out, -Data): Name-Values for every input of Out's program, from data/2.
inputs_data(Out, Data) :-
   compile:program(Out, Boxes), compile:names(Boxes, Names),
   include([N]>>(N \== Out, compile:boxes_of(N, [])), Names, Inputs),
   maplist([In, In-Vals]>>data(In, Vals), Inputs, Data).

data(Name, Vals) :-
   shape(Name, Shape), foldl([E, S0, S1]>>(S1 is S0*E), Shape, 1, N),
   numlist(1, N, Is), maplist(datum, Is, Vals).

% Centred, small values: a transformer's activations stay in range, with no denormals, which
% a CPU handles slowly.
datum(I, V) :- V is (float(I mod 97) / 97 - 0.5) * 0.2.

bench(Label, Out, Inputs, Device, Options0, Reps) :-
   maplist([In, In-Vals]>>data(In, Vals), Inputs, Data),
   bench_data(Label, Out, Data, Device, Options0, Reps).

once_run(Queue, Program, Buffers, Kernels) :- once_run(Queue, Program, Buffers, Kernels, _).
once_run(Queue, Program, Buffers, Kernels, T) :-
   get_time(T0),
   compile:run_plan(Queue, Program, Buffers, [], Kernels),
   cl_finish(Queue),
   get_time(T1), T is T1 - T0.

go(Device) :- go(Device, []).
go(Device, Opts) :-
   matmul(A, B, C, 512, 512, 512), bench('matmul 512^3 ', C, [A, B], Device, Opts, 5),
   matmul(A2, B2, C2, 1024, 1024, 1024), bench('matmul 1024^3', C2, [A2, B2], Device, Opts, 3),
   softmax(X, Y, 1024, 1024), bench('softmax 1024x1024', Y, [X], Device, [local(64)], 5),
   softmax(X2, Y2, 64, 4096), bench('softmax 64x4096 ', Y2, [X2], Device, [local(128)], 5),
   dot(DA, DB, S, 1048576), bench('dot 1M          ', S, [DA, DB], Device, [local(256)], 5).
