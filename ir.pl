:- module(ir, [
   load/3,
   store/3,
   cast/3,
   simd/1,
   parallel/1,
   ir_run/2,
   ir_verify/1,
   ir_formats/2
]).

/** <module> Kernel IR

The generic kernel IR specified in docs/kernel_ir.md: a kernel is a clause

    kernel(Out-Format, In1-Format1, ...) :- Body.

whose body is executable Prolog. This module holds the reference semantics
of its vocabulary (load/3, store/3, cast/3 and the annotations), runs a
kernel on Prolog data (ir_run/2), checks the invariants of the spec
(ir_verify/1), and infers the format of each value (ir_formats/2).
*/

:- use_module(library(apply)).
:- use_module(library(dcg/high_order)).
:- use_module(library(lists)).
:- use_module(library(pairs)).
:- use_module(buffer, [buffer_from_data/4, buffer_to_data/4]).

:- meta_predicate
   simd(0),
   parallel(0).

% Reference semantics
% ===================

% A buffer is Data-Format, with Data a data(...) term.
load(Buffer-_Format, Index, Value) :-
   I is Index + 1,
   arg(I, Buffer, Value).

% A value position holds a value expression: store/3 and cast/3 evaluate it.
store(Buffer-_Format, Index, Expr) :-
   I is Index + 1,
   Value is Expr,
   nb_setarg(I, Buffer, Value).

cast(Format, Expr, Out), float_format(Format) =>
   In is Expr,
   round_to_format(Format, In, Out).
cast(_, Expr, Out) =>
   Out is integer(Expr).

% A value rounds to a float format as C converts it, to the nearest with
% ties to even: through a one-element C buffer of buffer.pl.
round_to_format(Format, In, Out) :-
   buffer_from_data(Buffer, Format, 1, data(In)),
   buffer_to_data(Buffer, Format, 1, data(Out)).

% Annotations run their goal unchanged.
simd(Goal) :-
   call(Goal).
parallel(Goal) :-
   call(Goal).

% ir_run(+Kernel, +Datas)
% Runs Kernel, a kernel clause, with its buffers bound to Datas, data(...)
% terms in the order of its head. Outputs must have their size.
ir_run(Kernel, Datas) :-
   copy_term(Kernel, (Head :- Body)),
   Head =.. [_ | Buffers],
   pairs_keys(Buffers, Datas),
   call(Body).

% Formats
% =======

format(bool).
format(int8).
format(uint8).
format(int16).
format(uint16).
format(int32).
format(uint32).
format(int64).
format(uint64).
format(Format) :-
   float_format(Format).
% the Prolog device's exact formats
format(integer).
format(boolean).

float_format(float16).
float_format(float32).
float_format(float64).

% Verifying
% =========

% ir_verify(+Kernel)
% Kernel satisfies the invariants of the IR, or an error
% ir_error(Reason, Culprit) is raised. Nothing is bound.
ir_verify(Kernel) :-
   ir_formats(Kernel, _).

% ir_formats(+Kernel, -Formats)
% Formats pairs each value variable of Kernel with its format, in the order
% the variables are assigned. Index variables aren't values.
ir_formats(Kernel, Formats) :-
   kernel_buffers(Kernel, Buffers, Body),
   Env = env(Buffers, [], []),
   phrase(goal(Body, Env, _), Formats),
   accesses(Body, Buffers).

kernel_buffers((Head :- Body), Buffers, Body0), compound(Head) =>
   Head =.. [_ | Buffers],
   maplist(buffer, Buffers),
   distinct_buffers(Buffers),
   Body0 = Body.
kernel_buffers(Kernel, _, _) =>
   ir_error(not_a_kernel, Kernel).

buffer(Buffer-Format), var(Buffer), atom(Format), format(Format) =>
   true.
buffer(Buffer) =>
   ir_error(not_a_buffer, Buffer).

distinct_buffers([]) =>
   true.
distinct_buffers([B-_ | Buffers]), member(B1-_, Buffers), B1 == B =>
   ir_error(repeated_buffer, B).
distinct_buffers([_ | Buffers]) =>
   distinct_buffers(Buffers).

% env(Buffers, Indices, Values): the scope of a goal. Values pairs each value
% variable with its format, or with const for a number assigned by
% unification.

% goal(+Goal, +Env0, -Env)//
% Goal is valid in Env0 and defines the variables of Env. It emits the
% format of each value it assigns.
goal((A, B), Env0, Env) ==>
   goal(A, Env0, Env1),
   goal(B, Env1, Env).
goal(true, Env0, Env) ==>
   { Env = Env0 }.
goal(simd(Goal), Env0, Env) ==>
   goal(Goal, Env0, Env).
goal(parallel(Goal), Env0, Env) ==>
   goal(Goal, Env0, Env).
% the variables of a forall are local to it
goal(forall(Domain, Goal), Env0, Env) ==>
   goal(Domain, Env0, Env1),
   goal(Goal, Env1, _),
   { Env = Env0 }.
goal(between(Min, Max, I), Env0, Env) ==>
   { Min == 0, integer(Max) -> true ; ir_error(not_a_binder, between(Min, Max, I)) },
   { fresh(I, Env0) },
   { Env0 = env(Buffers, Indices, Values) },
   { Env = env(Buffers, [I | Indices], Values) }.
goal(load(Buffer, Index, Value), Env0, Env) ==>
   { known_buffer(Buffer, Env0) },
   { index(Index, Env0) },
   { Buffer = _-Format },
   assign(Value, Format, Env0, Env).
goal(store(Buffer, Index, Value), Env0, Env) ==>
   { known_buffer(Buffer, Env0) },
   { index(Index, Env0) },
   { value(Value, Env0) },
   { Env = Env0 }.
goal(Value is Expr, Env0, Env) ==>
   { expr_format(Expr, Env0, Format) },
   assign(Value, Format, Env0, Env).
goal(cast(Format, In, Out), Env0, Env) ==>
   { atom(Format), format(Format) -> true ; ir_error(not_a_format, Format) },
   { value(In, Env0) },
   assign(Out, Format, Env0, Env).
goal(Value = Number, Env0, Env), number(Number) ==>
   assign(Value, const, Env0, Env).
goal((Cond -> Then ; Else), Env0, Env) ==>
   { condition(Cond, Env0) },
   { phrase(goal(Then, Env0, ThenEnv), ThenFormats) },
   { phrase(goal(Else, Env0, ElseEnv), ElseFormats) },
   { branch_values(Env0, ThenEnv, ThenValues) },
   { branch_values(Env0, ElseEnv, ElseValues) },
   { merge_branches(ThenValues, ElseValues, Merged) },
   { branch_formats(ThenFormats, ElseFormats, Merged, Formats) },
   Formats,
   { Env0 = env(Buffers, Indices, Values) },
   { append(Merged, Values, Values1) },
   { Env = env(Buffers, Indices, Values1) }.
% the variables of the aggregated goal are local to it
goal(aggregate_all(Aggregate, Goal, Result), Env0, Env) ==>
   { aggregate(Aggregate, X) },
   { phrase(goal(Goal, Env0, GoalEnv), _) },
   { value_expression_format(X, GoalEnv, Format) },
   goal(Goal, Env0, _),
   assign(Result, Format, Env0, Env).
goal(Goal, _, _) ==>
   { ir_error(unknown_goal, Goal) }.

aggregate(sum(X), Y) =>
   Y = X.
aggregate(max(X), Y) =>
   Y = X.
aggregate(Aggregate, _) =>
   ir_error(unknown_aggregate, Aggregate).

% assign(+Var, +Format, +Env0, -Env)//
assign(Var, Format, Env0, Env) -->
   {  fresh(Var, Env0),
      Env0 = env(Buffers, Indices, Values),
      Env = env(Buffers, Indices, [Var-Format | Values])
   },
   format_pair(Var, Format).

format_pair(_, const) ==>
   [].
format_pair(Var, Format) ==>
   [Var-Format].

fresh(Var, Env), var(Var), \+ bound(Var, Env) =>
   true.
fresh(Var, _), var(Var) =>
   ir_error(assigned_twice, Var).
fresh(Term, _) =>
   ir_error(not_a_variable, Term).

bound(Var, env(Buffers, Indices, Values)) :-
   (  member(B-_, Buffers)
   ;  member(B, Indices)
   ;  member(B-_, Values)
   ),
   B == Var,
   !.

known_buffer(B-F, env(Buffers, _, _)), member(B0-F0, Buffers), B0 == B =>
   (  F0 == F
   -> true
   ;  ir_error(format_mismatch, B-F)
   ).
known_buffer(Buffer, _) =>
   ir_error(unknown_buffer, Buffer).

% An index is integer arithmetic over index variables.
index(Var, env(_, Indices, _)), var(Var) =>
   (  member(I, Indices), I == Var
   -> true
   ;  ir_error(not_an_index, Var)
   ).
index(N, _), integer(N) =>
   true.
index(Expr, Env), compound(Expr), index_op(Expr) =>
   Expr =.. [_ | Args],
   maplist(index_of(Env), Args).
index(Expr, _) =>
   ir_error(not_an_index, Expr).

index_of(Env, Index) :-
   index(Index, Env).

index_op(_ + _).
index_op(_ - _).
index_op(_ * _).
index_op(_ // _).
index_op(_ mod _).

% A condition compares indices, or values.
condition((A, B), Env) =>
   condition(A, Env),
   condition(B, Env).
condition(Cond, Env), compound(Cond), comparison(Cond) =>
   Cond =.. [_, A, B],
   operand(A, Env),
   operand(B, Env).
condition(Cond, _) =>
   ir_error(not_a_condition, Cond).

comparison(_ < _).
comparison(_ =< _).
comparison(_ > _).
comparison(_ >= _).
comparison(_ =:= _).
comparison(_ =\= _).

operand(X, env(_, Indices, _)), var(X), member(I, Indices), I == X =>
   true.
operand(X, Env) =>
   (  catch(index(X, Env), error(ir_error(_, _), _), fail)
   -> true
   ;  expr_format(X, Env, _)
   ).

% A value position holds a number, or a value expression.
value(Number, _), number(Number) =>
   true.
value(Expr, Env) =>
   expr_format(Expr, Env, _).

value_expression_format(Expr, Env, Format) :-
   expr_format(Expr, Env, Format).

value_format(Var, env(_, _, Values), Format), var(Var),
      member(V-F, Values), V == Var =>
   Format = F.
value_format(Var, _, _) =>
   ir_error(not_a_value, Var).

% The format of an expression is the format of its value operands, which
% must agree: the lowering casts them first.
expr_format(Expr, Env, Format) :-
   phrase(operand_formats(Expr, Env), Formats0),
   exclude(==(const), Formats0, Formats1),
   sort(Formats1, Formats),
   expr_format_(Formats, Expr, Format).

expr_format_([], Expr, Format), sub_term(random_float, Expr) =>
   Format = float64.
expr_format_([], Expr, _) =>
   ir_error(no_format, Expr).
expr_format_([Format0], _, Format) =>
   Format = Format0.
expr_format_(Formats, Expr, _) =>
   ir_error(mixed_formats(Formats), Expr).

operand_formats(Var, Env), var(Var) ==>
   { value_format(Var, Env, Format) },
   [Format].
operand_formats(N, _), number(N) ==>
   [].
operand_formats(random_float, _) ==>
   [].
operand_formats(Expr, Env), compound(Expr), value_op(Expr) ==>
   { Expr =.. [_ | Args] },
   sequence(operand_formats_of(Env), Args).
operand_formats(Expr, _) ==>
   { ir_error(not_a_value_expression, Expr) }.

operand_formats_of(Env, Arg) -->
   operand_formats(Arg, Env).

value_op(_ + _).
value_op(_ - _).
value_op(_ * _).
value_op(- _).
value_op(sin(_)).
value_op(log(_)).
value_op(sqrt(_)).
value_op(float(_)).
value_op(integer(_)).

% The values a branch assigns, beyond those of Env0.
branch_values(env(_, _, Values0), env(_, _, Values), New) :-
   length(Values0, N0),
   length(Values, N),
   K is N - N0,
   length(New, K),
   append(New, _, Values).

% The values a conditional assigns are those both branches assign: a value
% assigned by one branch only is local to it. A value assigned only numbers
% is a comparison's result, a bool.
merge_branches(Then, Else, Merged) :-
   convlist(merge_value(Else), Then, Merged).

merge_value(Else, Var-ThenFormat, Var-Format) :-
   member(V-ElseFormat, Else),
   V == Var,
   !,
   merge_format(ThenFormat, ElseFormat, Var, Format).

merge_format(const, const, _, Format) =>
   Format = bool.
merge_format(const, F, _, Format) =>
   Format = F.
merge_format(F, const, _, Format) =>
   Format = F.
merge_format(F, F0, _, Format), F == F0 =>
   Format = F.
merge_format(F1, F2, Var, _) =>
   ir_error(branch_formats(F1, F2), Var).

% The formats a conditional reports: its branches', and bool for a value
% both branches assign a number, a comparison's result.
branch_formats(ThenFormats, ElseFormats, Merged, Formats) :-
   exclude(reported(ThenFormats), ElseFormats, ElseOnly),
   append(ThenFormats, ElseOnly, Reported),
   include(unreported_bool(Reported), Merged, Bools),
   append(Reported, Bools, Formats).

unreported_bool(Reported, Var-Format) :-
   Format == bool,
   \+ reported(Reported, Var-_).

reported(Formats, Var-_) :-
   member(V-_, Formats),
   V == Var,
   !.

% A buffer is loaded or stored, not both, and the stored buffers, the
% outputs, come first.
accesses(Body, Buffers) :-
   phrase(access(Body), Accesses),
   maplist(access_position(Buffers), Accesses, Positions),
   findall(P, member(load(P), Positions), Loaded),
   findall(P, member(store(P), Positions), Stored),
   (  member(P, Loaded), memberchk(P, Stored)
   -> nth1(P, Buffers, B-_),
      ir_error(loaded_and_stored, B)
   ;  true
   ),
   (  member(L, Loaded), member(S, Stored), S > L
   -> nth1(S, Buffers, B-_),
      ir_error(outputs_not_first, B)
   ;  true
   ).

% access(+Goal)// : the load(Buffer) and store(Buffer) accesses of Goal.
access((A, B)) ==>
   access(A),
   access(B).
access((_ -> Then ; Else)) ==>
   access(Then),
   access(Else).
access(forall(_, Goal)) ==>
   access(Goal).
access(aggregate_all(_, Goal, _)) ==>
   access(Goal).
access(simd(Goal)) ==>
   access(Goal).
access(parallel(Goal)) ==>
   access(Goal).
access(load(B-_, _, _)) ==>
   [load(B)].
access(store(B-_, _, _)) ==>
   [store(B)].
access(_) ==>
   [].

access_position(Buffers, Access, Positioned) :-
   Access =.. [Kind, B],
   nth1(P, Buffers, B0-_),
   B0 == B,
   !,
   Positioned =.. [Kind, P].

:- multifile prolog:error_message//1.

prolog:error_message(ir_error(Reason, Culprit)) -->
   [ 'Invalid kernel IR: ~p: ~p'-[Reason, Culprit] ].

ir_error(Reason, Culprit) :-
   throw(error(ir_error(Reason, Culprit), _)).

:- begin_tests(ir).

% The examples of docs/kernel_ir.md.
example(matmul_add_raw, (kernel(O-float64, A-float64, B-float64, X-float64) :-
   forall(( between(0, 1, I1), between(0, 1, I2) ),
          ( aggregate_all(sum(P),
               ( between(0, 1, T),
                 load(A-float64,
                      ((I1*2 + I2)//2*4 + (I1*2 + I2) mod 2*2 + T)//4*2
                      + ((I1*2 + I2)//2*4 + (I1*2 + I2) mod 2*2 + T) mod 4//2*0
                      + ((I1*2 + I2)//2*4 + (I1*2 + I2) mod 2*2 + T) mod 4 mod 2*1,
                      VA),
                 load(B-float64,
                      ((I1*2 + I2)//2*4 + (I1*2 + I2) mod 2*2 + T)//4*0
                      + ((I1*2 + I2)//2*4 + (I1*2 + I2) mod 2*2 + T) mod 4//2*1
                      + ((I1*2 + I2)//2*4 + (I1*2 + I2) mod 2*2 + T) mod 4 mod 2*2,
                      VB),
                 P is VA*VB ),
               S),
            load(X-float64, I1*2 + I2, VX),
            V is S + VX,
            store(O-float64, I1*2 + I2, V) )))).
example(matmul_add, (kernel(O-float64, A-float64, B-float64, X-float64) :-
   forall(( between(0, 1, I1), between(0, 1, I2) ),
          ( aggregate_all(sum(P),
               ( between(0, 1, T),
                 load(A-float64, I1*2 + T, VA),
                 load(B-float64, T*2 + I2, VB),
                 P is VA*VB ),
               S),
            load(X-float64, I1*2 + I2, VX),
            V is S + VX,
            store(O-float64, I1*2 + I2, V) )))).
example(pad, (kernel(O-uint8, B-uint8) :-
   forall(between(0, 3, I),
          ( ( 1 =< I, I < 3 -> load(B-uint8, I - 1, VB) ; VB = 0 ),
            V is VB + 1,
            store(O-uint8, I, V) )))).
example(compare, (kernel(O-bool, A-uint32) :-
   forall(between(0, 1, I),
          ( load(A-uint32, I, VA0),
            cast(uint64, VA0, VA),
            P0 is VA*VA,
            cast(uint64, P0, P),
            ( P < 1000000000 -> V = 1 ; V = 0 ),
            store(O-bool, I, V) )))).
example(max_cast, (kernel(O-int8, A-float64) :-
   forall(between(0, 1, I),
          ( aggregate_all(max(X),
               ( between(0, 1, J),
                 load(A-float64, I*2 + J, VA),
                 P is VA*2.0,
                 cast(int8, P, X) ),
               M),
            store(O-int8, I, M) )))).
example(nested_sums, (kernel(O-uint8, A-uint8) :-
   forall(between(0, 1, I),
          ( aggregate_all(sum(Y),
               ( between(0, 1, J),
                 aggregate_all(sum(X),
                    ( between(0, 1, K),
                      load(A-uint8, I*4 + J*2 + K, X) ),
                    S0),
                 Y is S0*2 ),
               S),
            store(O-uint8, I, S) )))).
example(rand, (kernel(O-float64) :-
   forall(between(0, 3, I),
          ( V is random_float,
            store(O-float64, I, V) )))).

% run(Name, Inputs, Output): Output after running the example on Inputs.
run(Name, Inputs, Size, Output) :-
   example(Name, Kernel),
   functor(Output, data, Size),
   ir_run(Kernel, [Output | Inputs]).

test('the examples verify', [forall(example(_, Kernel))]) :-
   ir_verify(Kernel).

test('both matmuls compute the same', [forall(member(Name, [matmul_add_raw, matmul_add]))]) :-
   run(Name, [data(1, 2, 3, 4), data(5, 6, 7, 8), data(1, 1, 1, 1)], 4, O),
   O == data(20, 23, 44, 51).

test('a padded read stores 0 outside') :-
   run(pad, [data(2, 3)], 4, O),
   O == data(1, 3, 4, 1).

test('an inlined product is compared in uint64') :-
   run(compare, [data(70000, 3)], 2, O),
   O == data(0, 1).

test('a maximum of rounded floats') :-
   run(max_cast, [data(1.5, 2.6, 3.4, 0.2)], 2, O),
   O == data(5, 7).

test('nested sums') :-
   run(nested_sums, [data(1, 2, 3, 4, 5, 6, 7, 8)], 2, O),
   O == data(20, 52).

test('rand stores floats in [0, 1)') :-
   run(rand, [], 4, O),
   O =.. [data | Values],
   forall(member(V, Values), (float(V), V >= 0, V < 1)).

test('formats of a padded read') :-
   example(pad, Kernel),
   ir_formats(Kernel, Formats),
   Kernel = (_ :- forall(_, ((_ -> load(_, _, VB) ; _), V is _, _))),
   Formats == [VB-uint8, V-uint8].

test('formats of a comparison') :-
   example(compare, Kernel),
   ir_formats(Kernel, Formats),
   Kernel = (_ :- forall(_, (load(_, _, VA0), cast(_, _, VA), P0 is _, cast(_, _, P),
                             (_ -> V = 1 ; _), _))),
   Formats == [VA0-uint32, VA-uint64, P0-uint64, P-uint64, V-bool].

test('value positions evaluate their expressions') :-
   Kernel = (kernel(O-float32, A-float64) :-
                forall(between(0, 1, I),
                       ( aggregate_all(sum(VA*2), (between(0, 0, _), load(A-float64, I, VA)), S),
                         cast(float32, S + 0.1, V),
                         store(O-float32, I, V*1) ))),
   ir_verify(Kernel),
   Out = data(_, _),
   ir_run(Kernel, [Out, data(1.0, 2.0)]),
   Out == data(2.0999999046325684, 4.099999904632568).

test('a float cast rounds as C does') :-
   cast(float32, 0.1, X),
   X == 0.10000000149011612,
   cast(float16, 2049, Y),
   Y == 2048.0,
   cast(int8, 2.5, Z),
   Z == 3.

% broken(Reason, Kernel): Kernel breaks one invariant.
broken(assigned_twice, (kernel(O-int32) :-
   forall(between(0, 1, I), (V = 1, V = 2, store(O-int32, I, V))))).
broken(format_mismatch, (kernel(O-int32, A-int32) :-
   forall(between(0, 1, I), (load(A-int64, I, V), store(O-int32, I, V))))).
broken(loaded_and_stored, (kernel(O-int32) :-
   forall(between(0, 1, I), (load(O-int32, I, V), store(O-int32, I, V))))).
broken(unknown_goal, (kernel(O-int32) :-
   forall(between(0, 1, I), (nb_setarg(1, O, I), store(O-int32, I, 0))))).
broken(not_an_index, (kernel(O-int32, A-int32) :-
   forall(between(0, 1, I), (load(A-int32, I, V), load(A-int32, V, W), store(O-int32, I, W))))).
broken(outputs_not_first, (kernel(A-int32, O-int32) :-
   forall(between(0, 1, I), (load(A-int32, I, V), store(O-int32, I, V))))).
broken(mixed_formats([int32, int8]), (kernel(O-int32, A-int32, B-int8) :-
   forall(between(0, 1, I), (load(A-int32, I, VA), load(B-int8, I, VB),
                             V is VA + VB, store(O-int32, I, V))))).

test('a broken kernel is rejected', [forall(broken(Reason, Kernel))]) :-
   catch(ir_verify(Kernel), error(ir_error(Got, _), _), true),
   Got == Reason.

test('verifying binds nothing', [forall(example(_, Kernel))]) :-
   copy_term(Kernel, Copy),
   ir_verify(Kernel),
   Kernel =@= Copy.

:- end_tests(ir).
