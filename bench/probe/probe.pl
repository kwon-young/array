:- use_module(library(array)).
:- use_module(library(array/opencl)).
:- use_module(library(array/buffer)).

% The GPU matmul kernel under the derived options, and variants of its source, each timed alone:
% the staging alone, both without the barriers, and other unroll factors of the K block.

matmul(A, B, C, N, M, P) :-
   shape(A, [N, M]), shape(B, [M, P]), shape(C, [N, P]),
   over([I:N, J:P], [C[I, J] := 0]),
   over([I:N, J:P, K:M], [C[I, J] := C[I, J] + A[I, K] * B[K, J]]).

variant(full, L, L).
variant(staging_only, L, L1) :- exclude([S]>>sub_string(S, _, _, _, "fma("), L, L1).
variant(no_barriers, L, L1) :- exclude([S]>>sub_string(S, _, _, _, "barrier"), L, L1).
variant(kk_unroll_2, L, L1) :- kk_pragma(L, "  #pragma unroll 2", L1).
variant(kk_unroll_1, L, L1) :- kk_pragma(L, "  #pragma unroll 1", L1).

% The pragma line before the kk loop replaced.
kk_pragma([P, F | L], New, [New, F | L]) :- sub_string(P, _, _, _, "#pragma"), sub_string(F, _, _, _, "for (int kk"), !.
kk_pragma([X | L], New, [X | L1]) :- kk_pragma(L, New, L1).

probe(Device, N, Options) :-
   opencl_device(Device, Dev), device_options(Dev, Derived), merge_options(Options, Derived, Opts),
   matmul(A, B, C, N, N, N),
   kernels(C, Opts, [_, K]), source([K], Src),
   split_string(Src, "\n", "", Lines),
   compile:device(Device, Dev, Context, Queue),
   compile:work(K, Global, Local),
   maplist([X, X-[]]>>true, [A, B, C], _),
   N2 is N*N, Bytes is 4*N2,
   maplist([_, Mem]>>cl_buffer(Context, Bytes, Mem), [A, B, C], Mems),
   maplist([Mem, mem(Mem)]>>true, Mems, Args),
   forall(member(V, [full, staging_only, no_barriers, kk_unroll_2, kk_unroll_1]),
          ( variant(V, Lines, Lines1), atomic_list_concat(Lines1, "\n", Src1),
            cl_program(Context, Dev, Src1, "-cl-nv-verbose", Program), cl_kernel(Program, k0, Kernel),
            cl_program_log(Program, Dev, Log), registers(Log, Regs),
            cl_enqueue(Queue, Kernel, Args, Global, Local, [], _), cl_finish(Queue),
            findall(T, ( between(1, 5, _), get_time(T0), cl_enqueue(Queue, Kernel, Args, Global, Local, [], _),
                         cl_finish(Queue), get_time(T1), T is T1 - T0 ), Ts),
            min_list(Ts, Best), format("~w ~w^3 ~w: ~3f ms, ~w registers~n", [Device, N, V, Best*1000, Regs]) )).

registers(Log, Regs) :-
   (  sub_string(Log, B, _, _, "Used "), sub_string(Log, B, 20, _, S), split_string(S, " ", "", [_, R | _])
   -> number_string(Regs, R)
   ;  Regs = unknown
   ).

% The register report, the opcodes of the loads in the PTX, and the compute statement.
report(Device, N, Options) :-
   opencl_device(Device, Dev), device_options(Dev, Derived), merge_options(Options, Derived, Opts),
   matmul(_, _, C, N, N, N),
   kernels(C, Opts, [_, K]), source([K], Src),
   compile:device(Device, Dev, Context, _),
   cl_program(Context, Dev, Src, "-cl-nv-verbose", Program),
   cl_program_log(Program, Dev, Log), registers(Log, Regs), format("registers: ~w~n", [Regs]),
   cl_program_binary(Program, Ptx),
   split_string(Ptx, "\n\t ", "\n\t ;", Words),
   findall(Op, ( member(W, Words), atom_string(Op, W), ( sub_atom(Op, 0, _, _, 'ld.') ; sub_atom(Op, 0, _, _, 'st.') ;
                                                          sub_atom(Op, 0, _, _, 'fma') ; sub_atom(Op, 0, _, _, 'bar') ) ), Ops),
   msort(Ops, Sorted), clumped(Sorted, Counts),
   forall(member(Op-Cnt, Counts), format("  ~w ~w~n", [Cnt, Op])),
   split_string(Src, "\n", "", SrcLines),
   once(( member(SL, SrcLines), sub_string(SL, _, _, _, "fma(") )),
   sub_string(SL, 0, 260, _, Head), format("compute: ~w...~n", [Head]).
