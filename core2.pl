:- module(core2, [shape/2, elements/2, over/2, op(20, yf, [])]).
:- use_module(library(clpBNR)).

:- multifile error:has_type/2.

% Vocabulary. A name is a variable: it is never bound, only compared. An index is a plain
% variable; an axis I:N is an index I over an extent N, a clpBNR integer. A box over(Axes, Eqs)
% runs Eqs at each point of its axes, in lexicographic order. An equation A[Ts] := V writes
% the value V at the place A[Ts]: the name A subscripted by one target per axis of its shape;
% an equation may also be a box. A read A[Es] is the current content of a place, and a name
% alone is its rank-0 place. A variable in a value is an index in scope, a name, or a number:
% a clpBNR variable stands for a number. The definition of a name hangs on it as the
% attribute def(Shape, Boxes), the boxes writing it, in order. An input is a name no box
% writes. The left-hand side of an equation is the only thing that creates a name.

prim(+, 2).  prim(-, 2).  prim(-, 1).  prim(*, 2).  prim(/, 2).  prim(max, 2).  prim(min, 2).
prim(exp, 1).  prim(sqrt, 1).  prim(log, 1).  prim(<, 2).  prim(=<, 2).  prim(=:=, 2).

arith(E, Args) :-
   compound(E),
   E =.. [Op | Args],
   length(Args, Arity),
   prim(Op, Arity).

% The types check the pieces alone; well_formed/2 checks a box in its scope. The check of
% an extent declares it: a variable becomes a clpBNR integer, an expression gets one. An
% equation is checked to its places, a box inside one to its axes: its equations are checked
% in their own scope.
error:has_type(name, X) :- var(X).
error:has_type(index, X) :- var(X), \+ attvar(X).
error:has_type(extent, X) :- extent(X).
error:has_type(axis, X) :- nonvar(X), X = I:N, is_of_type(index, I), is_of_type(extent, N).
error:has_type(axes, X) :- is_of_type(list(axis), X), maplist(arg(1), X, Is), distinct(Is).
error:has_type(shape, X) :- is_of_type(list(extent), X).
error:has_type(bound, X) :- ground(X), !, catch(_ is X, _, fail).
error:has_type(bound, X) :- term_variables(X, Vs), forall(member(V, Vs), get_attr(V, clpBNR, _)).
error:has_type(place, X) :- place(X, A, Ts), var(A), is_of_type(list, Ts).
error:has_type(equation, X) :- nonvar(X), equation(X).

extent(X), compound(X) => N::integer(0, inf), {N == X}.
extent(X) => X::integer(0, inf).

equation(P := _) => is_of_type(place, P).
equation(over(Axes, Eqs)) => is_of_type(axes, Axes), is_of_type(list, Eqs).
equation(_) => fail.

distinct(Vars) :-
   sort(Vars, Sorted),
   same_length(Vars, Sorted).

place(A, Name, Targets), var(A) => Name = A, Targets = [].
place([](Ts, A), Name, Targets) => Name = A, Targets = Ts.
place(_, _, _) => fail.

% elements(?A, ?Lo-Hi): the elements of the name A lie in Lo..Hi: declared for an input, so
% that a read of it can be a subscript, a gather, checked by the bounds rule as the interval.
% A bound is a number or an expression in extents, D-1 for a subscript into D places.
elements(A, Range), get_attr(A, elements, R) => Range = R.
elements(A, Lo-Hi), var(A) => must_be(bound, Lo), must_be(bound, Hi), put_attr(A, elements, Lo-Hi).
elements(A, _) => type_error(name, A).

elements:attr_unify_hook(_, Other) :-
   throw(error(permission_error(bind, name, Other), _)).

% shape(?A, ?Shape): the shape of the name A, declaring A if it has none.
shape(A, Shape), get_attr(A, core2, def(Shape0, _)) => Shape = Shape0.
shape(A, Shape), var(A) => must_be(shape, Shape), put_attr(A, core2, def(Shape, [])).
shape(A, _) => type_error(name, A).

% over(+Axes, +Eqs): checks the box over(Axes, Eqs), and hangs it on every name it writes.
over(Axes, Eqs) :-
   Box = over(Axes, Eqs),
   well_formed([], Box),
   writes(Box, Names),
   maplist(define(Box), Names).

writes(over(_, Eqs), Names) :-
   foldl(lhs, Eqs, [], Names0),
   sort(Names0, Names).

lhs(over(_, Eqs), Names0, Names) => foldl(lhs, Eqs, Names0, Names).
lhs(P := _, Names0, Names) => place(P, A, _), Names = [A | Names0].

define(Box, A) :-
   get_attr(A, core2, def(Shape, Boxes)),
   append(Boxes, [Box], Boxes1),
   put_attr(A, core2, def(Shape, Boxes1)).

% well_formed(+Scope, +Term): Scope holds the axes around Term, innermost first. The indices
% of a box are new in its scope, the targets of a place are values and stay in its shape, a
% read is of a declared name, and a value mentions only what is in scope.
well_formed(Scope, over(Axes, Eqs)) =>
   must_be(axes, Axes),
   must_be(list(equation), Eqs),
   append(Axes, Scope, Scope1),
   must_be(axes, Scope1),
   maplist(well_formed(Scope1), Eqs).
well_formed(Scope, P := V) =>
   place(P, A, Ts),
   maplist(well_formed(Scope), Ts),
   target(Scope, A, Ts),
   well_formed(Scope, V).
well_formed(Scope, V), var(V) =>
   variable(Scope, V, Kind),
   scalar(Kind, V).
well_formed(_, N), number(N) =>
   true.
well_formed(Scope, R), place(R, A, Es) =>
   maplist(well_formed(Scope), Es),
   read(Scope, A, Es).
well_formed(Scope, where(C, T, E)) =>
   maplist(well_formed(Scope), [C, T, E]).
well_formed(Scope, E), arith(E, Args) =>
   maplist(well_formed(Scope), Args).
well_formed(_, E) =>
   type_error(value, E).

% variable(+Scope, +V, -Kind): a variable is an index, a name, or a number.
variable(Scope, V, Kind), in_scope(V, Scope) => Kind = index.
variable(_, V, Kind), get_attr(V, core2, def(Shape, _)) => Kind = name(Shape).
variable(_, V, Kind), get_attr(V, clpBNR, _) => Kind = number.
variable(_, V, _) => type_error(index, V).

scalar(index, _) => true.
scalar(number, _) => true.
scalar(name([]), _) => true.
scalar(name(_), V) => domain_error(rank(0), V).

in_scope(I, Scope) :-
   once(( member(J:_, Scope), J == I )).

% target(+Scope, +A, +Ts): A, a name of the rank of Ts, created at its first write, holds Ts.
% read(+Scope, +A, +Es): A, a declared name, holds Es.
target(Scope, A, _), in_scope(A, Scope) => type_error(name, A).
target(Scope, A, Ts), var(A), \+ get_attr(A, core2, _) =>
   same_length(Ts, Shape),
   shape(A, Shape),
   in_bounds(Scope, A, Ts).
target(Scope, A, Ts) => in_bounds(Scope, A, Ts).

read(Scope, A, Es), get_attr(A, core2, _) => in_bounds(Scope, A, Es).
read(_, A, _) => existence_error(name, A).

in_bounds(Scope, A, Ss) :-
   shape(A, Shape),
   fit(Scope, A, Ss, Shape).

fit(Scope, _, Ss, Shape), same_length(Ss, Shape) => maplist(subscript_in(Scope), Ss, Shape).
fit(_, A, Ss, Shape) => length(Shape, Rank), domain_error(rank(Rank), [](Ss, A)).

% subscript_in(+Scope, +S, +N): S, affine in the indices of Scope, stays in 0..N-1 at every
% point of Scope: a relation between the extents of Scope and N, which may be unknown. A read
% of a name with a range, a gather, stays in it by that range.
subscript_in(_, S, N), place(S, A, _), get_attr(A, elements, Lo-Hi) =>
   within(Lo, Hi, N, S).
subscript_in(Scope, S, N) =>
   affine(Scope, S, C, Terms),
   foldl(spread, Terms, C-C, Low-High),
   within(Low, High, N, S).

within(Low, High, N, _), {Low >= 0, High =< N-1} => true.
within(_, _, _, S) => domain_error(in_bounds, S).

spread(K-N, Low-High0, Bounds), K > 0 => Bounds = Low-(High0 + K*(N-1)).
spread(K-N, Low0-High, Bounds) => Bounds = (Low0 + K*(N-1))-High.

% affine(+Scope, +S, -C, -Terms): S is C plus the sum of K*I for each K-N of Terms, I the
% index of extent N; C is an expression in numbers.
affine(Scope, S, C, Terms) :-
   form(Scope, S, 1, 0-[], C-Pairs),
   keysort(Pairs, Sorted),
   group_pairs_by_key(Sorted, Groups),
   foldl(term(Scope), Groups, [], Terms).

% form(+Scope, +S, +K, +C0-Pairs0, -C-Pairs): C0 + K*S, with its index terms as I-K pairs.
form(S, A+B, K, Acc0, Acc) => form(S, A, K, Acc0, Acc1), form(S, B, K, Acc1, Acc).
form(S, A-B, K, Acc0, Acc) => form(S, A, K, Acc0, Acc1), K1 is -K, form(S, B, K1, Acc1, Acc).
form(S, -A, K, Acc0, Acc) => K1 is -K, form(S, A, K1, Acc0, Acc).
form(S, A*B, K, Acc0, Acc), number(A) => K1 is K*A, form(S, B, K1, Acc0, Acc).
form(S, A*B, K, Acc0, Acc), number(B) => K1 is K*B, form(S, A, K1, Acc0, Acc).
form(S, V, K, C-Pairs0, Acc), var(V), in_scope(V, S) => Acc = C-[V-K | Pairs0].
form(S, V, K, C0-Pairs, Acc), var(V), variable(S, V, number) => Acc = (C0 + K*V)-Pairs.
form(_, N, K, C0-Pairs, Acc), number(N) => Acc = (C0 + K*N)-Pairs.
form(_, E, _, _, _) => type_error(affine, E).

term(_, _-Ks, Terms0, Terms), sum_list(Ks, 0) => Terms = Terms0.
term(Scope, I-Ks, Terms0, Terms) => sum_list(Ks, K), extent(Scope, I, N), Terms = [K-N | Terms0].

extent(Scope, I, N) :-
   once(( member(J:N, Scope), J == I )).

% A name is never bound. The toplevel prints its shape and, under one of its names, each box.
attr_unify_hook(_, Other) :-
   throw(error(permission_error(bind, name, Other), _)).

attribute_goals(A) -->
   { get_attr(A, core2, def(Shape, Boxes)),
     include(owner(A), Boxes, Owned) },
   [shape(A, Shape)],
   Owned.

owner(A, Box) :-
   writes(Box, [First | _]),
   First == A.

:- begin_tests(core2).

x(X) :- shape(X, [3]).
y(Y) :- shape(Y, [2, 3]).

test(transpose, [timeout(10), true(S == [3, 2])]) :-
   y(Y),
   over([I:3, J:2], [T[I, J] := Y[J, I]]),
   shape(T, S0),
   S0 = [3, 2],
   S = S0.
test(shape_is_a_lower_bound, [timeout(10), fail]) :-
   y(Y),
   over([I:3, J:2], [T[I, J] := Y[J, I]]),
   shape(T, [2, 2]).
test(matmul_two_boxes, [timeout(10), true(N == 2)]) :-
   shape(A, [2, 3]), shape(B, [3, 4]), shape(C, [2, 4]),
   over([I:2, J:4], [C[I, J] := 0]),
   over([I:2, J:4, K:3], [C[I, J] := C[I, J] + A[I, K] * B[K, J]]),
   get_attr(C, core2, def(_, Boxes)),
   length(Boxes, N).
test(cumsum_extent_expression, [timeout(10), true(N == 5)]) :-
   shape(X, [N, 3]),
   over([J:3], [C[0, J] := X[0, J]]),
   over([T:N-1, J:3], [C[T+1, J] := C[T, J] + X[T+1, J]]),
   shape(C, [5, 3]),
   N = 5.
test(fibonacci_shifted_target, [timeout(10), fail]) :-
   over([], [F[0] := 1, F[1] := 1]),
   over([T:8], [F[T+2] := F[T] + F[T+1]]),
   shape(F, [9]).
test(rank_0_name, [timeout(10), true(S == [])]) :-
   x(X),
   over([], [Sum := 0]),
   over([K:3], [Sum := Sum + X[K]]),
   shape(Sum, S).
test(nested_box, [timeout(10), true(Ns == [1, 1])]) :-
   shape(F, [2, 2]), shape(X, [N, 2]),
   over([T:N-1], [over([I:2], [P[I] := 0]),
                  over([I:2, J:2], [P[I] := P[I] + F[I, J] * X[T, J]]),
                  over([I:2], [X[T+1, I] := P[I]])]),
   get_attr(P, core2, def(_, Bp)), get_attr(X, core2, def(_, Bx)),
   maplist(length, [Bp, Bx], Ns).
test(reads_relate_extents, [timeout(10), true(Lo == 3)]) :-
   shape(X, [N]),
   over([I:3], [_T[I] := X[I]]),
   range(N, [Lo, _]).
test(symbolic_constant, [timeout(10)]) :-
   shape(X, [N]),
   over([I:N], [_R[I] := X[N-1-I]]).
test(where_and_comparison, [timeout(10)]) :-
   x(X),
   over([I:3], [_R[I] := where(X[I] < 0, -X[I], X[I])]).

test(index_as_name, [timeout(10), throws(error(type_error(name, _), _))]) :-
   over([I:3], [I[0] := 1]).
test(name_as_index, [timeout(10), throws(error(type_error(axes, _), _))]) :-
   x(X),
   over([X:3], [_T[X] := 1]).
test(free_variable, [timeout(10), throws(error(type_error(index, _), _))]) :-
   x(X),
   over([I:3], [_T[I] := X[_]]).
test(undeclared_read, [timeout(10), throws(error(existence_error(name, _), _))]) :-
   over([I:3], [_T[I] := _X[I]]).
test(duplicate_axis, [timeout(10), throws(error(type_error(axes, _), _))]) :-
   over([I:3, I:2], [_T[I] := 1]).
test(inner_axis_shadows, [timeout(10), throws(error(type_error(axes, _), _))]) :-
   over([I:3], [over([I:2], [_T[I] := 1])]).
test(rank_mismatch, [timeout(10), throws(error(domain_error(rank(1), _), _))]) :-
   x(X),
   over([I:3, J:2], [_T[I, J] := X[I, J]]).
test(name_as_scalar, [timeout(10), throws(error(domain_error(rank(0), _), _))]) :-
   x(X),
   over([I:3], [_T[I] := X + 1]).
test(read_out_of_bounds, [timeout(10), throws(error(domain_error(in_bounds, _), _))]) :-
   x(X),
   over([I:3], [_T[I] := X[I+5]]).
test(write_out_of_bounds, [timeout(10), throws(error(domain_error(in_bounds, _), _))]) :-
   shape(T, [2]),
   over([I:3], [T[I] := 1]).
test(negative_subscript, [timeout(10), throws(error(domain_error(in_bounds, _), _))]) :-
   x(X),
   over([I:3], [_T[I] := X[2-I-1]]).
test(name_is_never_bound, [timeout(10), throws(error(permission_error(bind, name, _), _))]) :-
   x(X),
   X = foo.
test(not_a_shape, [timeout(10), throws(error(type_error(shape, _), _))]) :-
   shape(_, [2, foo]).
test(not_a_value, [timeout(10), throws(error(type_error(value, _), _))]) :-
   over([I:3], [_T[I] := foo(I)]).

% Beyond the structural check: a gather needs the range of the index array's elements, and
% a read of a place must come after its write.
test(gather, [timeout(10)]) :-
   shape(Idx, [4]), elements(Idx, 0-2), shape(H, [3]),
   over([K:4], [H[Idx[K]] := H[Idx[K]] + 1]).
test(gather_symbolic_range, [timeout(10), true(Lo == 3)]) :-
   shape(H, [N]), shape(Idx, [4]), elements(Idx, 0-(N-1)),
   over([K:4], [H[Idx[K]] := H[Idx[K]] + 1]),
   N = 3, range(N, [Lo, _]).
test(gather_range_above_extent, [timeout(10), throws(error(domain_error(in_bounds, _), _))]) :-
   shape(H, [N]), shape(Idx, [4]), elements(Idx, 0-N),
   over([K:4], [H[Idx[K]] := 1]).
test(gather_out_of_range, [timeout(10), throws(error(domain_error(in_bounds, _), _))]) :-
   shape(Idx, [4]), elements(Idx, 0-5), shape(H, [3]),
   over([K:4], [H[Idx[K]] := H[Idx[K]] + 1]).
test(gather_needs_a_range, [timeout(10), throws(error(type_error(affine, _), _))]) :-
   shape(Idx, [4]), shape(H, [3]),
   over([K:4], [H[Idx[K]] := 1]).
test(read_before_write, [timeout(10), fixme(needs_dependence_analysis),
                         throws(error(domain_error(written, _), _))]) :-
   over([T:8], [F[T] := F[T+1]]).

:- end_tests(core2).
