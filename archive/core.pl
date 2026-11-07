:- op(20, yf, []).
:- use_module(library(record)).
:- use_module(library(clpBNR)).

:- multifile error:has_type/2.

% Vocabulary. An array has axes [I:2, J:3]: an axis I:2 is an index I and its extent 2. Its
% shape is [2, 3], its rank 2 and its size 6. A point [1, 2] gives each index a coordinate;
% its offset is 5. An input holds data; an array and a rec have a body, an expression of
% their indices; a read A[I+1, J] has subscripts [I+1, J]. A rec reads itself as Self.

monoid(+, 0).
monoid(*, 1).
arith(A+B, +, [A, B]).
arith(A-B, -, [A, B]).
arith(A*B, *, [A, B]).
arith(A<B, <, [A, B]).
arith(A=<B, =<, [A, B]).
arith(A=:=B, =:=, [A, B]).

error:has_type(index, X) :- var(X).
error:has_type(extent, X) :- X::integer(0, inf).
error:has_type(axis, X) :- nonvar(X), X = I:N, is_of_type(index, I), is_of_type(extent, N).
error:has_type(axes, X) :- is_of_type(list(axis), X), distinct_indices(X).
error:has_type(shape, X) :- is_of_type(list(extent), X).
error:has_type(coordinate, X) :- is_of_type(nonneg, X).
error:has_type(point, X) :- is_of_type(list(coordinate), X).
error:has_type(offset, X) :- is_of_type(nonneg, X).
error:has_type(data, X) :- is_of_type(list(number), X).
error:has_type(monoid, X) :- atom(X), monoid(X, _).
error:has_type(array, X) :- well_formed(X).

distinct_indices(Axes) :-
   maplist(axis_index, Axes, Indices),
   sort(Indices, Sorted),
   same_length(Sorted, Indices).

% well_formed(@Array): an array is checked as a whole, as its body only means something with
% its axes in scope. The data of an input fills its shape. The body of an array or a rec
% mentions only its indices and those of the aggs around it; a rec, which has at least its
% time axis, also reads itself.
well_formed(input(Shape, Data)) =>
   is_of_type(shape, Shape),
   is_of_type(data, Data),
   prod_list(Shape, Size),
   length(Data, Size).
well_formed(array(Axes, Body)) =>
   is_of_type(axes, Axes),
   maplist(axis_index, Axes, Scope),
   well_formed(Scope, none, Body).
well_formed(rec(Self, Axes, Body)), var(Self) =>
   is_of_type(axes, Axes),
   Axes = [_Time | _],
   maplist(axis_index, Axes, Scope),
   \+ in_scope(Self, Scope),
   length(Axes, Rank),
   well_formed(Scope, self(Self, Rank), Body).
well_formed(_) => fail.

% well_formed(+Scope, +Self, @Expr): Expr mentions only the indices of Scope, and reads
% Self, if it is self(Self, Rank), or an array, with one subscript per axis.
well_formed(Scope, _, Index), var(Index) =>
   in_scope(Index, Scope).
well_formed(_, _, Number), number(Number) =>
   true.
well_formed(Scope, Self, [](Subscripts, Array)) =>
   is_of_type(list, Subscripts),
   maplist(well_formed(Scope, Self), Subscripts),
   read_rank(Self, Array, Rank),
   length(Subscripts, Rank).
well_formed(Scope, Self, agg(Monoid, Axis, Body)) =>
   is_of_type(monoid, Monoid),
   is_of_type(axis, Axis),
   axis_index(Axis, Index),
   \+ in_scope(Index, Scope),
   \+ self(Self, Index),
   well_formed([Index | Scope], Self, Body).
well_formed(Scope, Self, where(If, Then, Else)) =>
   well_formed(Scope, Self, If),
   well_formed(Scope, Self, Then),
   well_formed(Scope, Self, Else).
well_formed(Scope, Self, Expr), arith(Expr, _, Args) =>
   maplist(well_formed(Scope, Self), Args).
well_formed(_, _, _) => fail.

in_scope(Index, Scope) :-
   once(( member(I, Scope), I == Index )).

self(self(Self, _), Var) :-
   Self == Var.

% An array read was checked when it was made: only its rank matters here.
read_rank(self(Self, Rank0), Array, Rank), Self == Array =>
   Rank = Rank0.
read_rank(_, Array, Rank), nonvar(Array), array_term(Array) =>
   rank(Array, Rank).
read_rank(_, _, _) => fail.

array_term(input(_, _)).
array_term(array(_, _)).
array_term(rec(_, _, _)).

in_bounds(Scope, Self, [](Subscripts, Array)) =>
   maplist(in_bounds(Scope, Self), Subscripts),
   (  Self == none
   -> shape(Array, Shape)
   ;  shape(Self, Shape)
   ),
   maplist(subscript_in(Scope), Subscripts, Shape).

subscript_in(Scope, Subscript, Extent) :-
   affine(Subscript, Affine),
   hull(Scope, Affine, High, Low),
   { Low >= 0, High =< Extent-1 }.

affine(A+B, Affine) =>
   affine(A, A1),
   affine(B, B1),
   add(A1, B1, Affine).
affine(A*B, Affine) =>
   affine(A, A1),
   affine(B, B1),
   (  A1 = affine(C, [], 0)
   -> scale(C, B1, Affine)
   ;  B1 = affine(C, [], 0)
   -> scale(C, A1, Affine)
   ;  A1 = affine(C1, L1, R1),
      B1 = affine(C2, L2, R2),
      scale(C1, L2, C1L2),
      scale(C2, L1, C2L1),
      add(C1L2, C2L1, L),
      Affine = affine(C1*C2, L, C1*R2+C2*R1+L1*L2+L1*R2+L2*R1+R1*R2)
   ).

% add(+Affine1, +Affine2, -Affine): the terms on the same index merge into one; a coefficient
% that sums to 0 drops its term.
add(affine(C1, L1, R1), affine(C2, L2, R2), affine(C, L, R)) :-
   sum(C1, C2, C),
   append(L1, L2, L3),
   keysort(L3, Sorted),
   group_pairs_by_key(Sorted, Groups),
   foldl(merge, Groups, L, []),
   sum(R1, R2, R).

merge(I-Cs, L0, L) :-
   foldl(sum, Cs, 0, C),
   merge(C, I, L0, L).

merge(C, _, L0, L), C == 0 => L0 = L.
merge(C, I, L0, L) => L0 = [I-C | L].

% sum(+A, +B, -C): C is the expression A+B, with numbers folded.
sum(A, B, C), number(A), number(B) => C is A+B.
sum(A, B, C), A == 0 => C = B.
sum(A, B, C), B == 0 => C = A.
sum(A, B, C) => C = A+B.

% The records give the accessors and check the fields alone; well_formed/1 checks the whole.
:- record input(shape: shape, data: data).
:- record array(axes: axes, body).
:- record rec(self: var, axes: axes, body).

axis_index(I:_, I).
axis_extent(_:N, N).

shape(input(Shape0, _), Shape) => Shape = Shape0.
shape(array(Axes, _), Shape) => maplist(axis_extent, Axes, Shape).
shape(rec(_, Axes, _), Shape) => maplist(axis_extent, Axes, Shape).
rank(Array, Rank) :-
   shape(Array, Shape),
   length(Shape, Rank).
size(Array, Size) :-
   shape(Array, Shape),
   prod_list(Shape, Size).

prod_list([], 1).
prod_list([Extent | Shape], Prod) :-
   { Prod == Extent * Sub },
   prod_list(Shape, Sub).
input(Shape, [H | T], Input) =>
   prod_list(Shape, Size),
   when((ground(Size) ; ground([H | T])), length([H | T], Size)),
   make_input([shape(Shape), data([H | T])], Input),
   must_be(array, Input).
array(Axes, Body, Array) :-
   make_array([axes(Axes), body(Body)], Array),
   must_be(array, Array).
rec(Self, Axes, Body, Rec) :-
   make_rec([self(Self), axes(Axes), body(Body)], Rec),
   must_be(array, Rec).
% over(Axes, Body, array(Axes, Body)) :-
%    pairs_keys_values(Env, Axes, Inferred),
%    maplist(coordinate, Inferred),
%    check(Env, Body).
%
% check(Axes, [](Subscripts, Array)) :-
%    shape(Array, Shape),
%    check(Axes, Subscripts, Shape).
%
% check(_Axes, [], _).
% check(Axes, [Subscript | Subscripts], [Extent | Shape]) :-
%    infer(Axes, Subscript, Infer),
%    range(Infer, [Low, Sup]),
%    Sup < Extent,
%    Low >= 0,
%    check(Axes, Subscripts, Shape).
%
% coordinate(Extent, Coordinate) :-
%    Coordinate::integer(0, inf),
%    { Coordinate < Extent }.
%
% infer(Axes, Var, Infer), var(Var), member(I:Extent, Axes), I == Var =>
%    Infer::integer(0, inf),
%    { Infer < Extent }.
% infer(_Axes, Number, Infer), number(Number) =>
%    Infer = Number.
% infer(Axes, A+B, Infer) =>
%    infer(Axes, A, A1),
%    infer(Axes, B, B1),
%    { Infer == A1+B1 }.
% infer(Axes, A*B, Infer) =>
%    infer(Axes, A, A1),
%    infer(Axes, B, B1),
%    { Infer == A1*B1 }.
%
% at(input(Shape, Data), Point, Value) :-
%    linearize(Shape, Point, Offset),
%    when((ground(Offset) ; ground(Value)), nth0(Offset, Data, Value)).
% at(array(Axes, Body), Point, Value) :-
%    pairs_keys_values(Env, Axes, Point),
%    eval(Env, Body, Value).
% at(rec(Self, Axes, Body), Point, Value) :-
%    pairs_keys_values(Env, Axes, Point),
%    eval([rec(Self)-rec(Self, Axes, Body) | Env], Body, Value).
%
% eval(Env, [](Subscripts, Array), Value), member(rec(Self)-Rec, Env), Self == Array =>
%    maplist(eval(Env), Subscripts, Point),
%    at(Rec, Point, Value).
% eval(Env, [](Subscripts, Array), Value) =>
%    maplist(eval(Env), Subscripts, Point),
%    at(Array, Point, Value).
% eval(Env, agg(+, Axis, Body), Value) =>
%    acc(Env, Axis, Body, 0, 0, Value).
% eval(Env, where(If, Then, Else), Value) =>
%    eval(Env, If, Cond),
%    nth0(Cond, [Else, Then], Expr),
%    eval(Env, Expr, Value).
% eval(Env, A<B, Value) =>
%    eval(Env, A, A1),
%    eval(Env, B, B1),
%    (  A1<B1
%    -> Value = 1
%    ; Value = 0
%    ).
% eval(Env, A=:=B, Value) =>
%    eval(Env, A, A1),
%    eval(Env, B, B1),
%    (  A1=:=B1
%    -> Value = 1
%    ; Value = 0
%    ).
% eval(Env, A*B, Value) =>
%    eval(Env, A, A1),
%    eval(Env, B, B1),
%    Value is A1*B1.
% eval(Env, A+B, Value) =>
%    eval(Env, A, A1),
%    eval(Env, B, B1),
%    Value is A1+B1.
% eval(Env, A-B, Value) =>
%    eval(Env, A, A1),
%    eval(Env, B, B1),
%    Value is A1-B1.
% eval(Env, Index, Value), member((I:_Extent)-Coordinate, Env), I == Index =>
%    Value = Coordinate.
% eval(_Env, Number, Value), number(Number) =>
%    Value = Number.
%
% acc(Env, Index:Extent, Body, Coordinate, In, Out) :-
%    (  Extent == Coordinate
%    -> Out = In
%    ;  eval([(Index:Extent)-Coordinate | Env], Body, X),
%       Coordinate1 is Coordinate + 1,
%       Tmp is In + X,
%       acc(Env, Index:Extent, Body, Coordinate1, Tmp, Out)
%    ).
%
% multiply_add(Extent, Coordinate, In, Out) :-
%    Coordinate::integer(0, inf),
%    { Coordinate < Extent },
%    { Out == In*Extent + Coordinate }.
% linearize([Extent | Shape], [Coordinate | Point], Offset) :-
%    Coordinate::integer(0, inf),
%    { Coordinate < Extent },
%    foldl(multiply_add, Shape, Point, Coordinate, Sum),
%    {Offset == Sum}.

:- begin_tests(well_formed).

x(X) :- input([3], [1, 2, 3], X).
y(Y) :- input([2, 3], [1, 2, 3, 4, 5, 6], Y).

test(transpose, [timeout(10)]) :-
   y(Y),
   array([I:3, J:2], Y[J, I], _).
test(matvec, [timeout(10)]) :-
   x(X), y(Y),
   array([I:2], agg(+, K:3, Y[I, K] * X[K]), _).
test(nested, [timeout(10)]) :-
   x(X),
   array([I:3], X[I] + 1, A),
   array([J:3], A[2 - J], _).
test(index_shared_between_arrays, [timeout(10)]) :-
   x(X),
   array([I:3], X[I], A),
   array([I:3], A[I], _).
test(fibonacci, [timeout(10)]) :-
   rec(S, [T:8], where(T < 2, 1, S[T-1] + S[T-2]), _).
test(rec_eval, [timeout(10), true(V == 8)]) :-
   rec(S, [T:4], where(T < 1, 1, S[T-1] * 2), R),
   at(R, [3], V).

test(free_index, [timeout(10), throws(error(type_error(array, _), _))]) :-
   x(X),
   array([_:3], X[_], _).
test(index_as_array, [timeout(10), throws(error(type_error(array, _), _))]) :-
   array([I:3], I[0], _).
test(agg_reuses_axis_index, [timeout(10), throws(error(type_error(array, _), _))]) :-
   x(X),
   array([K:3], agg(+, K:2, X[K]), _).
test(agg_reuses_self, [timeout(10), throws(error(type_error(array, _), _))]) :-
   rec(S, [_:3], agg(+, S:2, 1), _).
test(self_rank, [timeout(10), throws(error(type_error(array, _), _))]) :-
   rec(S, [T:3], S[T, T, T], _).
test(self_as_value, [timeout(10), throws(error(type_error(array, _), _))]) :-
   rec(S, [T:3], S + T, _).
test(self_is_index, [timeout(10), throws(error(type_error(array, _), _))]) :-
   rec(S, [S:3], 1, _).
test(rec_without_time_axis, [timeout(10), throws(error(type_error(array, _), _))]) :-
   rec(_, [], 1, _).
test(data_does_not_fill_shape, [timeout(10), throws(error(type_error(array, _), _))]) :-
   make_input([shape([2]), data([1, 2, 3])], In),
   must_be(array, In).
test(handmade_array, [timeout(10), fail]) :-
   is_of_type(array, array([_:3], foo)).

% Value-level errors: they need bounds analysis, not a structural check.
test(rec_reads_current_state, [timeout(10), fixme(needs_analysis), throws(error(type_error(array, _), _))]) :-
   rec(S, [T:3], S[T], _).
test(out_of_bounds, [timeout(10), fixme(needs_analysis), throws(error(type_error(array, _), _))]) :-
   x(X),
   array([I:3], X[I+5], _).

:- end_tests(well_formed).

:- begin_tests(extent).

test(integer, [timeout(10)]) :-
   is_of_type(extent, 3).
test(not_an_extent, [timeout(10), forall(member(X, [-1, 2.0, 2.5, foo, f(x)])), fail]) :-
   is_of_type(extent, X).
test(var_becomes_extent, [timeout(10)]) :-
   is_of_type(extent, N),
   \+ N = -1,
   \+ N = 2.5,
   N = 4.
test(real_interval_becomes_integer, [timeout(10)]) :-
   N::real(0, 5),
   is_of_type(extent, N),
   \+ N = 2.5,
   N = 3.
test(negative_interval, [timeout(10), fail]) :-
   N::integer(-5, -1),
   is_of_type(extent, N).
test(input_infers_extent, [timeout(10), true(N == 2)]) :-
   input([N, 3], [1, 2, 3, 4, 5, 6], _).
test(input_two_unknown_extents, [timeout(10), true(M == 3)]) :-
   input([N, M], [1, 2, 3, 4, 5, 6], _),
   N = 2.
test(input_extent_cannot_fill_data, [timeout(10), throws(error(type_error(shape, _), _))]) :-
   input([_, 4], [1, 2, 3, 4, 5, 6], _).
test(array_extent_given_later, [timeout(10), true(V == 3)]) :-
   input([3], [1, 2, 3], X),
   array([I:N], X[I], A),
   N = 3,
   at(A, [2], V).
test(array_extent_negative_later, [timeout(10), fail]) :-
   input([3], [1, 2, 3], X),
   array([I:N], X[I], _),
   N = -1.
test(rec_time_extent_given_later, [timeout(10), true(V == 8)]) :-
   rec(S, [T:N], where(T < 1, 1, S[T-1] * 2), R),
   N = 4,
   at(R, [3], V).

:- end_tests(extent).
