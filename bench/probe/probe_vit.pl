:- use_module(library(array)).
:- use_module('../bench').
:- use_module('../../examples/nn').
:- set_prolog_flag(stack_limit, 4_000_000_000).

t(Device) :-
   S = 256, D = 768, H = 12, F = 3072,
   vit_block(_X, Y, S, D, H, F),
   compile:device(Device, Dev, _, _), device_options(Dev, Opts),
   compile:kernels(Y, Opts, Plan), compile:flat_plan(Plan, Flat), length(Flat, NK), format("kernels ~d~n", [NK]),
   forall(nth0(Idx, Flat, K), try(Device, Idx, K)).

try(Device, Idx, K) :-
   get_dict(kind, K, Kind),
   ( Kind == groups -> kernel{rows: Rows, local: Loc} :< K, Desc = groups(Rows, Loc)
   ; kernel{par: Par, stage: St} :< K, ( St = stage(G, TK, Tiles) -> length(Tiles, NT), St1 = stage(G, TK, NT) ; St1 = St ),
     compile:work(K, [], Global, Local), Desc = items(Par, St1, Global, Local) ),
   compile:device(Device, Dev, Context, Queue),
   K1 = K.put(id, 0),
   compile:source([K1], Src), compile:built(Context, Dev, Src, Program),
   get_dict(names, K, Names),
   maplist(compile:device_buffer(Context, Queue, []), Names, Mems), pairs_keys_values(Buffers, Names, Mems),
   catch(( once_run(Queue, Program, Buffers, [K1]), findall(T0, ( between(1, 3, _), once_run(Queue, Program, Buffers, [K1], T0) ), Ts),
            min_list(Ts, T), format("~d ~w  ~3f ms~n", [Idx, Desc, T*1000]) ),
         E, ( format("~d ~w  ERROR ~w~n", [Idx, Desc, E]),
              retractall(compile:device_state(_, _, _, _)), retractall(compile:program_state(_, _, _)) )).
