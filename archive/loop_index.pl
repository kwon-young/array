:- module(loop_index, [loop_index/1]).

/** <module> Loop indices

A loop index is a fresh variable marked by the attribute loop_index: the
index of a loop of a kernel, which no value of the array graph binds. Each
loop has its own, so nested loops never mix their indices.
*/

% loop_index(-K): K is a new loop index.
loop_index(K) :-
   put_attr(K, loop_index, true).

% A loop index is never bound nor unified.
attr_unify_hook(_, _) :-
   fail.
