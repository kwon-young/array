:- module(bench_minimalloc, [go_minimalloc/0]).
:- use_module(library(array/minimalloc)).

% The challenging problems of the original minimalloc project, each under the heuristic
% that solves it fastest, as files in minimalloc/ next to this one.

challenging_heuristic('A.1048576.out.csv', twa).
challenging_heuristic('B.1048576.out.csv', taw).
challenging_heuristic('C.1048576.out.csv', taw).
challenging_heuristic('D.1048576.out.csv', wat).
challenging_heuristic('E.1048576.out.csv', twa).
challenging_heuristic('F.1048576.out.csv', twa).
challenging_heuristic('G.1048576.out.csv', twa).
challenging_heuristic('H.1048576.out.csv', taw).
challenging_heuristic('I.1048576.out.csv', twa).
challenging_heuristic('J.1048576.out.csv', twa).
challenging_heuristic('K.1048576.csv', twa).

:- prolog_load_context(directory, Dir),
   directory_file_path(Dir, minimalloc, Data),
   assertz(data_directory(Data)).

go_minimalloc :-
   findall(File-H, challenging_heuristic(File, H), FilesHeuristics),
   maplist(benchmark, FilesHeuristics, Times),
   sum_list(Times, Total),
   format("Total: ~3f seconds~n", [Total]).

benchmark(File-Heuristic, Wall) :-
   data_directory(Dir),
   directory_file_path(Dir, File, Path),
   minimalloc:csv_read_buffers(Path, Buffers),
   call_time(minimalloc(Buffers, [heuristics([Heuristic])]), Time),
   get_dict(wall, Time, Wall),
   format("~w: ~3f seconds~n", [File, Wall]).
