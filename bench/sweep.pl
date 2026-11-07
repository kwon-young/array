:- [bench].
:- use_module('../examples/linalg').
% sweep(+Device, +N, +Extra): the matmul N^3 under a grid of schedules, best time each.
sweep(Device, N, Extra) :-
   forall(( member(Tiles, [[4, 4], [4, 8], [8, 8]]), member(G, [4, 8]), member(TK, [8, 16, 32]),
            N mod (G * 8) =:= 0 ),
          ( matmul(A, B, C, N, N, N),
            format(atom(L), "~w ~w g~w tk~w", [Extra, Tiles, G, TK]),
            catch(bench(L, C, [A, B], Device, [tile(Tiles), group(G), stage(TK) | Extra], 3), E, (print_message(error, E))) )).
sweeps(Device, N) :- sweep(Device, N, [major(k_first)]), sweep(Device, N, [major(k_last)]).
