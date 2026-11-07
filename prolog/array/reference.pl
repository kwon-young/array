:- module(reference, [evaluate/4]).
:- use_module(library(apply)).
:- use_module(library(lists)).
:- use_module(library(pairs)).
:- use_module(library(filesex)).
:- use_module(core).
:- use_module(buffer).

/** <module> The reference evaluation of a program

evaluate/4 runs the boxes of a program in Prolog, exactly, on data(...) terms: the semantics of
compile:eval/3. The boxes are compiled to one clause before they run: an axis is a failure
driven loop over between/3, an element N[Ts] is arg/3 or nb_setarg/3 of N's term at an offset
whose strides are numbers, and an expression is one is/2, but for a where/3, which runs one
branch only, and a comparison, which is 1 or 0.

With the flag eval_cache set, the elements of the output are kept on disk, under the SHA-1 of
the compiled clause, the initial terms of the names and the Prolog version: a program evaluated
once on some data is never evaluated again, in this process or the next. The clause holds every
extent, stride and bound as a number, so that it is all of the program the evaluation depends
on. The directory is the flag eval_cache_directory, by default array_eval under
$XDG_CACHE_HOME or ~/.cache; deleting it is always safe. A file is written under a temporary
name then renamed, so that concurrent writers, threads or processes, leave a whole file.
*/

:- create_prolog_flag(eval_cache, false, [type(boolean), keep(true)]).
:- create_prolog_flag(eval_cache_directory, '', [type(atom), keep(true)]).

% evaluate(+Out, +Boxes, +Env, -Values): the boxes run on Env, pairs Name-data(...) holding the
% initial elements of every name of Boxes and Out; Values the elements of Out after.
evaluate(Out, Boxes, Env, Values) :-
   compile(Boxes, Env, Code),
   pairs_keys_values(Env, Names, Terms),
   nth1(I, Names, Out1), Out1 == Out, !,
   current_prolog_flag(eval_cache, Cache),
   evaluate(Cache, Code, I, Terms, Values).

evaluate(true, Code, I, Terms, Values) =>
   current_prolog_flag(version, Prolog),
   variant_sha1(key(Prolog, Code, I, Terms), Key),
   cache_file(Key, File),
   cached(File, Code, I, Terms, Values).
evaluate(false, Code, I, Terms, Values) =>
   run(Code, I, Terms, Values).

cached(File, _, _, _, Values), exists_file(File) =>
   setup_call_cleanup(open(File, read, In, [type(binary)]), fast_read(In, Values), close(In)).
cached(File, Code, I, Terms, Values) =>
   run(Code, I, Terms, Values),
   store(File, Values).

store(File, Values) :-
   file_directory_name(File, Dir),
   make_directory_path(Dir),
   thread_self(Me), thread_property(Me, id(Id)),
   current_prolog_flag(pid, Pid),
   format(atom(Tmp), "~w.~w.~w.tmp", [File, Pid, Id]),
   setup_call_cleanup(open(Tmp, write, Out, [type(binary)]), fast_write(Out, Values), close(Out)),
   rename_file(Tmp, File).

cache_file(Key, File) :-
   cache_directory(Dir),
   sub_atom(Key, 0, 2, _, Sub),
   atomic_list_concat([Dir, Sub, Key], /, File).

cache_directory(Dir), current_prolog_flag(eval_cache_directory, D), D \== '' => Dir = D.
cache_directory(Dir), getenv('XDG_CACHE_HOME', Home), Home \== '' =>
   directory_file_path(Home, array_eval, Dir).
cache_directory(Dir) =>
   expand_file_name('~/.cache', [Home]),
   directory_file_path(Home, array_eval, Dir).

% run(+Code, +I, +Terms, -Values): the clause run on Terms, Values the elements of the Ith.
% The clause is one of code/1, local to the thread, for as long as it runs.
:- thread_local code/1.

run(code(Vars, Body), I, Terms, Values) :-
   assertz((code(Vars) :- Body), Ref),
   call_cleanup(code(Terms), erase(Ref)),
   nth1(I, Terms, Term),
   Term =.. [_ | Values].

% Compilation
% ===========

% compile(+Boxes, +Env, -Code): Code is code(Vars, Body), Body the goals running Boxes on the
% names of Env bound to Vars, in order; no attributed variable is left.
compile(Boxes, Env, code(Vars, Body)) :-
   pairs_keys(Env, Names),
   same_length(Names, Vars),
   pairs_keys_values(Ctx, Names, Vars),
   foldl(box(Ctx, []), Boxes, Goals, []),
   list_conj(Goals, Body),
   term_attvars(Body, []).

list_conj([], Conj) => Conj = true.
list_conj([G], Conj) => Conj = G.
list_conj([G | Gs], Conj) => Conj = (G, Conj1), list_conj(Gs, Conj1).

% box(+Ctx, +Idx, +Eq)//: the goals running Eq, with Idx the pairs Index-Var of the axes around.
box(Ctx, Idx, over([], Eqs)) -->
   foldl(box(Ctx, Idx), Eqs).
box(Ctx, Idx, over([I:E | Axes], Eqs)) -->
   { compile:extent(E, N), Last is N-1,
     phrase(box(Ctx, [I-V | Idx], over(Axes, Eqs)), Goals),
     list_conj(Goals, Inner) },
   [\+ ( between(0, Last, V), \+ Inner )].
box(Ctx, Idx, P := E) -->
   { core:place(P, N, Ts) },
   element(Ctx, Idx, N, Ts, Term, Arg),
   expr(Ctx, Idx, E, X),
   [Y is X, nb_setarg(Arg, Term, Y)].

% element(+Ctx, +Idx, +N, +Ts, -Term, -Arg)//: the element N[Ts] is argument Arg of Term, a
% number or a variable the goals bind.
element(Ctx, Idx, N, Ts, Term, Arg) -->
   { member(N1-Term, Ctx), N1 == N, !,
     shape(N, Shape),
     maplist(compile:extent, Shape, Ms) },
   offset(Ts, Ms, Ctx, Idx, 0, Off),
   arg_index(Off, Arg).

arg_index(Off, Arg), integer(Off) ==> { Arg is Off+1 }.
arg_index(Off, Arg) ==> [Arg is Off+1].

offset([], [], _, _, Off0, Off) --> { Off = Off0 }.
offset([T | Ts], [M | Ms], Ctx, Idx, Off0, Off) -->
   expr(Ctx, Idx, T, X),
   { plus_times(Off0, M, X, Off1) },
   offset(Ts, Ms, Ctx, Idx, Off1, Off).

plus_times(0, _, X, Off) => Off = X.
plus_times(Off0, M, X, Off) => Off = Off0*M + X.

% expr(+Ctx, +Idx, +E, -X)//: X is an arithmetic expression of the value of E once the goals
% have run.
expr(_, Idx, V, X), var(V), member(I-X0, Idx), I == V ==> { X = X0 }.
expr(Ctx, Idx, V, X), var(V) ==> read(Ctx, Idx, V, [], X).
expr(_, _, N, X), number(N) ==> { X = N }.
expr(Ctx, Idx, R, X), core:place(R, N, Ts) ==> read(Ctx, Idx, N, Ts, X).
expr(Ctx, Idx, where(C, T, E), X) ==>
   expr(Ctx, Idx, C, B),
   { branch(Ctx, Idx, T, X, Then), branch(Ctx, Idx, E, X, Else) },
   [( B =:= 0 -> Else ; Then )].
expr(Ctx, Idx, bits(A), X) ==>
   expr(Ctx, Idx, A, XA),
   [F is XA, float_bits(F, X)].
expr(Ctx, Idx, E, X), compound(E), E =.. [Op, A, B], memberchk(Op, [<, =<, =:=]) ==>
   expr(Ctx, Idx, A, XA), expr(Ctx, Idx, B, XB),
   { G =.. [Op, XA, XB] },
   [( G -> X = 1 ; X = 0 )].
expr(Ctx, Idx, E, X) ==>
   { E =.. [Op | As] },
   foldl(expr(Ctx, Idx), As, Xs),
   { X =.. [Op | Xs] }.

% float_bits(+F, -I): I is the int whose bits are those of F as a float32, through a buffer.
float_bits(F, I) :-
   buffer_from_data(B, float32, 1, data(F)),
   buffer_to_data(B, int32, 1, data(I)).

% branch(+Ctx, +Idx, +E, -X, -Goal): Goal binds X to the value of E, run alone.
branch(Ctx, Idx, E, X, Goal) :-
   phrase(expr(Ctx, Idx, E, X0), Goals, [X is X0]),
   list_conj(Goals, Goal).

read(Ctx, Idx, N, Ts, X) -->
   element(Ctx, Idx, N, Ts, Term, Arg),
   [arg(Arg, Term, X)].
