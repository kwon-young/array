:- module(ir_prolog, [ir_prolog/2]).

/** <module> The Prolog dialect of the kernel IR

The IR is Prolog already: the Prolog device runs a kernel clause after
inlining its helpers, for speed.
*/

:- use_module(library(pairs)).
:- use_module(ir, []).

% ir_prolog(+Kernel, -Clause)
% Clause is the Prolog device's clause for Kernel: its head takes the data of
% the buffers, loads and stores are inlined to arg/3 and nb_setarg/3, casts
% are arithmetic, and annotations are dropped.
ir_prolog((Head0 :- Body0), Clause) =>
   Head0 =.. [Name | Buffers],
   pairs_keys(Buffers, Datas),
   Head =.. [Name | Datas],
   goal(Body0, Body),
   Clause = (Head :- Body).

goal((A, B), Goal) =>
   goal(A, GA),
   goal(B, GB),
   Goal = (GA, GB).
goal((Cond -> Then ; Else), Goal) =>
   goal(Then, GThen),
   goal(Else, GElse),
   Goal = (Cond -> GThen ; GElse).
goal(forall(Domain, Body), Goal) =>
   goal(Body, GBody),
   Goal = forall(Domain, GBody).
goal(aggregate_all(Aggregate, Body, Result), Goal) =>
   goal(Body, GBody),
   Goal = aggregate_all(Aggregate, GBody, Result).
goal(simd(Body), Goal) =>
   goal(Body, Goal).
goal(parallel(Body), Goal) =>
   goal(Body, Goal).
goal(load(Data-_, Index, Value), Goal) =>
   Goal = (I is Index + 1, arg(I, Data, Value)).
goal(store(Data-_, Index, Value), Goal), var(Value) =>
   Goal = (I is Index + 1, nb_setarg(I, Data, Value)).
goal(store(Data-_, Index, Expr), Goal) =>
   Goal = (I is Index + 1, Value is Expr, nb_setarg(I, Data, Value)).
goal(cast(Format, In, Out), Goal) =>
   cast(Format, In, Out, Goal).
goal(Goal0, Goal) =>
   Goal = Goal0.

% float64 is Prolog's float, and integers are exact: other float formats round
% through ir:cast/3.
cast(float64, In, Out, Goal) =>
   Goal = (Out is float(In)).
cast(Format, In, Out, Goal), integer_format(Format) =>
   Goal = (Out is integer(In)).
cast(Format, In, Out, Goal) =>
   Goal = ir:cast(Format, In, Out).

integer_format(integer).
integer_format(boolean).
integer_format(bool).
integer_format(int8).
integer_format(uint8).
integer_format(int16).
integer_format(uint16).
integer_format(int32).
integer_format(uint32).
integer_format(int64).
integer_format(uint64).
