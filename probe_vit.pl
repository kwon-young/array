:- use_module(core2).
:- use_module(compile2).
:- use_module(bench2).
:- set_prolog_flag(stack_limit, 4_000_000_000).

t(Device) :-
   S = 256, D = 768, H = 12, F = 3072,
   vit_block(_X, Y, S, D, H, F),
   compile2:device(Device, Dev, _, _), device_options(Dev, Opts),
   compile2:kernels(Y, Opts, Plan), compile2:flat_plan(Plan, Flat), length(Flat, NK), format("kernels ~d~n", [NK]),
   forall(nth0(Idx, Flat, K), try(Device, Idx, K)).

try(Device, Idx, K) :-
   get_dict(kind, K, Kind),
   ( Kind == groups -> kernel{rows: Rows, local: Loc} :< K, Desc = groups(Rows, Loc)
   ; kernel{par: Par, stage: St} :< K, ( St = stage(G, TK, Tiles) -> length(Tiles, NT), St1 = stage(G, TK, NT) ; St1 = St ),
     compile2:work(K, [], Global, Local), Desc = items(Par, St1, Global, Local) ),
   compile2:device(Device, Dev, Context, Queue),
   K1 = K.put(id, 0),
   compile2:source([K1], Src), compile2:built(Context, Dev, Src, Program),
   get_dict(names, K, Names),
   maplist(compile2:device_buffer(Context, Queue, []), Names, Mems), pairs_keys_values(Buffers, Names, Mems),
   catch(( once_run(Queue, Program, Buffers, [K1]), findall(T0, ( between(1, 3, _), once_run(Queue, Program, Buffers, [K1], T0) ), Ts),
            min_list(Ts, T), format("~d ~w  ~3f ms~n", [Idx, Desc, T*1000]) ),
         E, ( format("~d ~w  ERROR ~w~n", [Idx, Desc, E]),
              retractall(compile2:device_state(_, _, _, _)), retractall(compile2:program_state(_, _, _)) )).
