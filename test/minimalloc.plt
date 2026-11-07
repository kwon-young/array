:- module(minimalloc_tests, []).

:- use_module(library(array/minimalloc)).

% input.12.csv is a problem of the original minimalloc project, with a capacity of 12.
:- prolog_load_context(directory, Dir),
   directory_file_path(Dir, 'input.12.csv', File),
   assertz(input_12(File)).

:- begin_tests(minimalloc).

test(input12, [timeout(10)]) :-
   input_12(File),
   minimalloc:csv_read_buffers(File, Buffers, []),
   minimalloc(Buffers, [capacity(12), heuristics([wat])]).

:- end_tests(minimalloc).
