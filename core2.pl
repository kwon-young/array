:- module(core2, [shape/2, elements/2, kind/2, label_kinds/1, power_of_two/1, permutation/1, over/2,
                  op(20, yf, [])]).
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
%
% The elements of a name have a kind: bool, int or float, in that order.
% A kind is a clpBNR integer in 0..2, hanging on the name as the attribute kind.
% The kind of a written name is the greatest kind of the values written to it.
% The kind of an input is declared by kind/2, or float when nothing narrows it.
% label_kinds/1 resolves the kinds of a program's names before it is compiled or run.
%
% A subscript is a value of kind int.
% Its hull over the points of its box is a pair of terms in the extents, posted to clpBNR once:
% the affine part in the indices is exact, and each other operation bounds its operands' hulls,
% themselves split the same way, so that an affine expression nested in a remainder stays exact.
% A division, a remainder, a shift and the bit operations take non-negative operands;
% xor and \/ need both operands below a power of two, a number or an extent declared by
% power_of_two/1.
% bits(F) is the int whose bits are those of the float F, as the device holds it.
% permutation/1 declares the elements of an int name distinct, so that a write through it,
% A[P[I]], is to distinct places along I: the compiler keeps I parallel.

prim(+, 2).  prim(-, 2).  prim(-, 1).  prim(*, 2).  prim(/, 2).  prim(max, 2).  prim(min, 2).
prim(exp, 1).  prim(sqrt, 1).  prim(log, 1).  prim(<, 2).  prim(=<, 2).  prim(=:=, 2).
prim(//, 2).  prim(mod, 2).  prim(>>, 2).  prim(<<, 2).  prim(/\, 2).  prim(\/, 2).  prim(xor, 2).
prim(bits, 1).

% int_op(?Op): an operation on ints alone.
int_op(//).  int_op(mod).  int_op(>>).  int_op(<<).  int_op(/\).  int_op(\/).  int_op(xor).

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

% kind(?A, ?Kind): the kind of the elements of the name A, bool, int or float.
% Declared on an input, it may come before its shape; read on any name, it is known once labelled.
kind(A, Kind), var(A) => name_kind(A, K), kind_name(A, Kind, K).
kind(A, _) => type_error(name, A).

% name_kind(+A, -K): the kind of A as a clpBNR integer, created at its first use.
name_kind(A, K), get_attr(A, kind, K0) => K = K0.
name_kind(A, K) => K::integer(0, 2), put_attr(A, kind, K).

kind_name(_, Kind, K), integer(K) => nth0(K, [bool, int, float], Kind).
kind_name(A, Kind, K), nonvar(Kind) =>
   must_be(oneof([bool, int, float]), Kind),
   once(nth0(K0, [bool, int, float], Kind)),
   (  K = K0
   -> true
   ;  domain_error(kind(Kind), A)
   ).
kind_name(_, Kind, K) => when(ground(K), nth0(K, [bool, int, float], Kind)).

kind:attr_unify_hook(_, Other) :-
   throw(error(permission_error(bind, name, Other), _)).

kind:attribute_goals(_) --> [].

% power_of_two(+N): the extent N is a power of two: checked on a number, declared on a variable,
% which the bounds rule of xor reads, and related to its exponent for clpBNR.
power_of_two(N), integer(N) =>
   (  N > 0, N /\ (N-1) =:= 0
   -> true
   ;  domain_error(power_of_two, N)
   ).
power_of_two(N), var(N) =>
   extent(N),
   put_attr(N, pow2, true),
   K::integer(0, 62),
   {N == 2**K}.
power_of_two(N) =>
   type_error(extent, N).

pow2:attr_unify_hook(_, N) :-
   (  integer(N), N > 0, N /\ (N-1) =:= 0
   -> true
   ;  throw(error(domain_error(power_of_two, N), _))
   ).

pow2:attribute_goals(N) --> [power_of_two(N)].

% permutation(+A): the elements of the int name A are distinct.
permutation(A), var(A) =>
   name_kind(A, K),
   holds(K =< 1, A),
   put_attr(A, perm, true).
permutation(A) =>
   type_error(name, A).

perm:attr_unify_hook(_, Other) :-
   throw(error(permission_error(bind, name, Other), _)).

perm:attribute_goals(A) --> [permutation(A)].

% label_kinds(+Names): the kinds of Names resolved.
% An input takes the one kind its uses leave it, float when they leave all three, int when they rule float out.
% A written name takes the least kind its values allow.
label_kinds(Names) :-
   partition(written, Names, Written, Inputs),
   maplist(label_input, Inputs),
   maplist(label_written, Written).

written(A) :-
   get_attr(A, core2, def(_, [_ | _])).

label_input(A) :-
   name_kind(A, K),
   (  integer(K)
   -> true
   ;  range(K, [Lo, Hi]),
      (  Lo =:= Hi
      -> K = Lo
      ;  Hi =:= 2
      -> K = 2
      ;  K = 1
      )
   ).

label_written(A) :-
   name_kind(A, K),
   (  integer(K)
   -> true
   ;  range(K, [Lo, _]),
      K = Lo
   ).

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
   well_formed(Scope, V),
   value_kind(Scope, V, Kv),
   name_kind(A, Ka),
   holds(Ka >= Kv, P := V).
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

% value_kind(+Scope, +V, -K): the kind of the well-formed value V, a clpBNR integer in 0..2.
% An index or an extent is an int, a number has the least kind holding it, a read has its name's.
% A comparison is a bool.
% A division, a root, an exponential and a logarithm are floats.
% The other operations take the greatest kind of their operands, an int at the least: arithmetic on bools is on ints.
% A where takes the greatest kind of its branches, and its condition is a bool.
value_kind(Scope, V, K), var(V) => variable(Scope, V, Kind), variable_kind(Kind, V, K).
value_kind(_, N, K), number(N) => number_kind(N, K).
value_kind(_, R, K), place(R, A, _) => name_kind(A, K).
value_kind(Scope, where(C, T, E), K) =>
   value_kind(Scope, C, Kc),
   holds(Kc == 0, C),
   value_kind(Scope, T, Kt),
   value_kind(Scope, E, Ke),
   kmax(Kt, Ke, K).
value_kind(Scope, E, K), arith(E, Args) =>
   maplist(value_kind(Scope), Args, Ks),
   E =.. [Op | _],
   op_kind(Op, E, Ks, K).

variable_kind(index, _, K) => K = 1.
variable_kind(number, _, K) => K = 1.
variable_kind(name(_), V, K) => name_kind(V, K).

number_kind(N, K), ( N == 0 ; N == 1 ) => K = 0.
number_kind(N, K), integer(N) => K = 1.
number_kind(_, K) => K = 2.

op_kind(Op, _, _, K), memberchk(Op, [<, =<, =:=]) => K = 0.
op_kind(Op, _, _, K), memberchk(Op, [/, sqrt, exp, log]) => K = 2.
op_kind(bits, _, _, K) => K = 1.
op_kind(Op, E, Ks, K), int_op(Op) => maplist(at_most_int(E), Ks), K = 1.
op_kind(_, _, Ks, K) => foldl(kmax, Ks, 1, K).

kmax(A, B, K) :-
   K::integer(0, 2),
   {K == max(A, B)}.

% at_most_int(+Culprit, +K): the kind K is held to int; a forall would undo the constraint.
at_most_int(Culprit, K) :-
   holds(K =< 1, Culprit).

% holds(+Constraint, +Culprit): the kind constraint is posted, or Culprit is of the wrong kind.
holds(Constraint, Culprit) :-
   (  {Constraint}
   -> true
   ;  domain_error(kind, Culprit)
   ).

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

% subscript_in(+Scope, +S, +N): S, a value of kind int, stays in 0..N-1 at every point of
% Scope: its hull, terms in the extents of Scope and N, posted as one constraint, a relation
% between extents which may be unknown.
subscript_in(Scope, S, N) :-
   value_kind(Scope, S, K),
   holds(K =< 1, S),
   hull(Scope, S, Low, High),
   within(Low, High, N, S).

within(Low, High, N, _), {Low >= 0, High =< N-1} => true.
within(_, _, _, S) => domain_error(in_bounds, S).

% hull(+Scope, +E, -Low, -High): bounds on the int expression E over the points of Scope: its
% affine part exactly, from the extents of its indices, and each remainder by the rule of its
% operation on the hulls of its operands, split the same way.
hull(Scope, E, Low, High) :-
   affine(Scope, E, C, Terms),
   foldl(spread(Scope), Terms, C-C, Low0-High0),
   simplify(Low0, Low),
   simplify(High0, High).

spread(_, K-N, Low-High0, Bounds), K > 0 => Bounds = Low-(High0 + K*(N-1)).
spread(_, K-N, Low0-High, Bounds) => Bounds = (Low0 + K*(N-1))-High.
spread(Scope, rest(K, E), Low0-High0, Bounds), K > 0 =>
   remainder(Scope, E, Lo, Hi), Bounds = (Low0 + K*Lo)-(High0 + K*Hi).
spread(Scope, rest(K, E), Low0-High0, Bounds) =>
   remainder(Scope, E, Lo, Hi), Bounds = (Low0 + K*Hi)-(High0 + K*Lo).

% remainder(+Scope, +E, -Lo, -Hi): the hull of a remainder E: a read in its range; a product
% of non-negatives; a quotient by the divmod relation, exact; a remainder below its divisor;
% a shift as a product or a quotient by a power of two; and below the least mask of its
% operands, and xor or \/ below their greatest, each a mask; max, min and where by their parts.
remainder(_, R, Lo, Hi), place(R, A, _) =>
   (  get_attr(A, elements, Lo0-Hi0)
   -> Lo = Lo0, Hi = Hi0
   ;  existence_error(elements, R)
   ).
remainder(Scope, A*B, Lo, Hi) =>
   hull(Scope, A, La, Ha), hull(Scope, B, Lb, Hb),
   nonneg(La, A*B), nonneg(Lb, A*B),
   Lo = La*Lb, Hi = Ha*Hb.
remainder(Scope, A // B, Lo, Hi) =>
   hull(Scope, A, La, Ha), hull(Scope, B, Lb, Hb),
   nonneg(La, A // B), positive(Lb, A // B),
   quotient(La, Hb, Lo), quotient(Ha, Lb, Hi).
remainder(Scope, A mod B, Lo, Hi) =>
   hull(Scope, A, La, Ha), hull(Scope, B, Lb, Hb),
   nonneg(La, A mod B), positive(Lb, A mod B),
   Lo = 0, Hi = min(Ha, Hb - 1).
remainder(Scope, A >> B, Lo, Hi) =>
   hull(Scope, A, La, Ha), shift(B, A >> B, P),
   nonneg(La, A >> B),
   quotient(La, P, Lo), quotient(Ha, P, Hi).
remainder(Scope, A << B, Lo, Hi) =>
   hull(Scope, A, La, Ha), shift(B, A << B, P),
   nonneg(La, A << B),
   Lo = La*P, Hi = Ha*P.
remainder(Scope, A /\ B, Lo, Hi) =>
   hull(Scope, A, La, Ha), hull(Scope, B, Lb, Hb),
   nonneg(La, A /\ B), nonneg(Lb, A /\ B),
   Lo = 0, Hi = min(Ha, Hb).
remainder(Scope, E, Lo, Hi), E =.. [Op, A, B], memberchk(Op, [\/, xor]) =>
   hull(Scope, A, La, Ha), hull(Scope, B, Lb, Hb),
   nonneg(La, E), nonneg(Lb, E), mask(Ha, E), mask(Hb, E),
   Lo = 0, Hi = max(Ha, Hb).
remainder(Scope, E, Lo, Hi), E =.. [Op, A, B], memberchk(Op, [max, min]) =>
   hull(Scope, A, La, Ha), hull(Scope, B, Lb, Hb),
   Lo =.. [Op, La, Lb], Hi =.. [Op, Ha, Hb].
remainder(Scope, where(_, T, E), Lo, Hi) =>
   hull(Scope, T, Lt, Ht), hull(Scope, E, Le, He),
   Lo = min(Lt, Le), Hi = max(Ht, He).
remainder(_, E, _, _) =>
   domain_error(bounded, E).

% nonneg(+Lo, +Culprit) and positive(+Lo, +Culprit): the bound Lo is at least 0, or 1, by its
% form: a number, an extent, a sum, a product, a max or a min of such.
nonneg(Lo, Culprit) :-
   (  at_least(Lo, 0)
   -> true
   ;  domain_error(non_negative, Culprit)
   ).

positive(Lo, Culprit) :-
   (  at_least(Lo, 1)
   -> true
   ;  domain_error(positive, Culprit)
   ).

at_least(N, B), number(N) => N >= B.
at_least(V, B), var(V) => range(V, [Lo, _]), number(Lo), Lo >= B.
at_least(A+C, B) => at_least(A, B), at_least(C, 0) ; at_least(A, 0), at_least(C, B).
at_least(A*C, B), B =< 0 => at_least(A, 0), at_least(C, 0).
at_least(A*C, B) => at_least(A, B), at_least(C, 1) ; at_least(A, 1), at_least(C, B).
at_least(max(A, C), B) => ( at_least(A, B) ; at_least(C, B) ).
at_least(min(A, C), B) => at_least(A, B), at_least(C, B).
at_least(_, _) => fail.

% quotient(+A, +B, -Q): Q is A // B: a number, or the integer of the divmod relation
% A = B*Q + R, 0 =< R < B, which clpBNR keeps exact.
quotient(A, B, Q), number(A), number(B) => Q is A // B.
quotient(A, B, Q) =>
   Q::integer, R::integer(0, inf),
   {A == B*Q + R, R =< B - 1}.

% shift(+B, +Culprit, -P): the shift B is a non-negative number, P the power of two it is.
shift(B, _, P), integer(B), B >= 0 => P is 1 << B.
shift(_, Culprit, _) => domain_error(shift, Culprit).

% mask(+Hi, +Culprit): the bound Hi is one below a power of two: a number, an extent declared
% by power_of_two/1 less one, or the max of two masks.
mask(Hi, Culprit) :-
   (  is_mask(Hi)
   -> true
   ;  domain_error(power_of_two, Culprit)
   ).

is_mask(N), integer(N) => N >= 0, N /\ (N+1) =:= 0.
is_mask(N-1), var(N) => get_attr(N, pow2, _).
is_mask(max(A, B)) => is_mask(A), is_mask(B).
is_mask(_) => fail.

% simplify(+T0, -T): T0 with its numbers folded and its identities dropped: the terms stay
% symbolic in the extents, for clpBNR to take whole.
simplify(T0, T), number(T0) => T = T0.
simplify(T0, T), var(T0) => T = T0.
simplify(T0, T), T0 =.. [Op, A0, B0], memberchk(Op, [+, -, *, min, max]) =>
   simplify(A0, A), simplify(B0, B), fold(Op, A, B, T).
simplify(T0, T) => T = T0.

fold(Op, A, B, T), number(A), number(B) => T0 =.. [Op, A, B], T is T0.
fold(+, A, B, T), A == 0 => T = B.
fold(+, A, B, T), B == 0 => T = A.
fold(-, A, B, T), B == 0 => T = A.
fold(*, A, B, T), ( A == 0 ; B == 0 ) => T = 0.
fold(*, A, B, T), A == 1 => T = B.
fold(*, A, B, T), B == 1 => T = A.
fold(Op, A, B, T) => T =.. [Op, A, B].

% affine(+Scope, +S, -C, -Terms): S is C plus the sum of K*I for each K-N of Terms, I the
% index of extent N, plus K*E for each rest(K, E), E a remainder; C is an expression in
% numbers.
affine(Scope, S, C, Terms) :-
   form(Scope, S, 1, 0-[], C-Pairs),
   keysort(Pairs, Sorted),
   group_pairs_by_key(Sorted, Groups),
   foldl(term(Scope), Groups, [], Terms).

% form(+Scope, +S, +K, +C0-Pairs0, -C-Pairs): C0 + K*S, with its index terms as I-K pairs and
% its remainders as r(E)-K pairs.
form(S, A+B, K, Acc0, Acc) => form(S, A, K, Acc0, Acc1), form(S, B, K, Acc1, Acc).
form(S, A-B, K, Acc0, Acc) => form(S, A, K, Acc0, Acc1), K1 is -K, form(S, B, K1, Acc1, Acc).
form(S, -A, K, Acc0, Acc) => K1 is -K, form(S, A, K1, Acc0, Acc).
form(S, A*B, K, Acc0, Acc), number(A) => K1 is K*A, form(S, B, K1, Acc0, Acc).
form(S, A*B, K, Acc0, Acc), number(B) => K1 is K*B, form(S, A, K1, Acc0, Acc).
form(S, V, K, C-Pairs0, Acc), var(V), in_scope(V, S) => Acc = C-[V-K | Pairs0].
form(S, V, K, C0-Pairs, Acc), var(V), variable(S, V, number) => Acc = (C0 + K*V)-Pairs.
form(_, N, K, C0-Pairs, Acc), number(N) => Acc = (C0 + K*N)-Pairs.
form(_, E, K, C-Pairs0, Acc), compound(E) => Acc = C-[r(E)-K | Pairs0].
form(_, E, _, _, _) => type_error(affine, E).

term(_, _-Ks, Terms0, Terms), sum_list(Ks, 0) => Terms = Terms0.
term(_, r(E)-Ks, Terms0, Terms) => sum_list(Ks, K), Terms = [rest(K, E) | Terms0].
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
   kind_goal(A),
   Owned.

kind_goal(A) --> { get_attr(A, kind, K), integer(K), nth0(K, [bool, int, float], Kind) }, !, [kind(A, Kind)].
kind_goal(_) --> [].

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

% Kinds: inferred forwards from the values written, backwards from the uses of an input, and
% labelled once the program is built.
test(kind_float_accumulation, [timeout(10), true(K == float)]) :-
   x(X),
   over([I:3], [S[I] := 0]),
   over([I:3], [S[I] := S[I] + X[I]]),
   label_kinds([X, S]), kind(S, K).
test(kind_count_is_int, [timeout(10), true(K == int)]) :-
   x(X),
   over([I:3], [C[I] := 0]),
   over([I:3], [C[I] := C[I] + where(X[I] < 0, 1, 0)]),
   label_kinds([X, C]), kind(C, K).
test(kind_comparison_is_bool, [timeout(10), true(K == bool)]) :-
   x(X),
   over([I:3], [B[I] := X[I] < 0]),
   label_kinds([X, B]), kind(B, K).
test(kind_division_is_float, [timeout(10), true(K == float)]) :-
   over([I:3], [T[I] := I / 2]),
   label_kinds([T]), kind(T, K).
test(kind_index_arithmetic_is_int, [timeout(10), true(K == int)]) :-
   over([I:3], [T[I] := I + 1]),
   label_kinds([T]), kind(T, K).
test(kind_input_defaults_to_float, [timeout(10), true(K == float)]) :-
   x(X),
   over([I:3], [_T[I] := X[I]]),
   label_kinds([X]), kind(X, K).
test(kind_declared_before_shape, [timeout(10), true(K == int)]) :-
   kind(Idx, int), shape(Idx, [4]), elements(Idx, 0-2), shape(H, [3]),
   over([K4:4], [H[Idx[K4]] := 1]),
   label_kinds([Idx, H]), kind(Idx, K).
test(kind_where_condition_narrows_input, [timeout(10), true(K == bool)]) :-
   x(X),
   over([I:3], [_T[I] := where(X[I], 1, 0)]),
   label_kinds([X]), kind(X, K).
test(kind_subscript_defaults_to_int, [timeout(10), true(K == int)]) :-
   shape(Idx, [4]), elements(Idx, 0-2), shape(H, [3]),
   over([K4:4], [H[Idx[K4]] := 1]),
   label_kinds([Idx, H]), kind(Idx, K).
test(kind_float_subscript, [timeout(10), throws(error(domain_error(kind, _), _))]) :-
   shape(Idx, [4]), elements(Idx, 0-2), kind(Idx, float), shape(H, [3]),
   over([K4:4], [H[Idx[K4]] := 1]).
test(kind_where_condition_not_bool, [timeout(10), throws(error(domain_error(kind, _), _))]) :-
   x(X), kind(X, float),
   over([I:3], [_T[I] := where(X[I], 1, 0)]).
test(kind_declared_too_low, [timeout(10), throws(error(domain_error(kind, _), _))]) :-
   shape(S, [3]), kind(S, bool),
   over([I:3], [S[I] := 2]).
test(kind_unknown, [timeout(10), throws(error(type_error(oneof(_), _), _))]) :-
   x(X), kind(X, double).
test(kind_bits_is_int_of_anything, [timeout(10), true(K == int)]) :-
   x(X),
   over([I:3], [B[I] := bits(X[I])]),
   label_kinds([X, B]), kind(B, K).
test(permutation_is_int, [timeout(10), true(K == int)]) :-
   shape(P, [4]), permutation(P),
   label_kinds([P]), kind(P, K).
test(permutation_of_a_float, [timeout(10), throws(error(domain_error(kind, _), _))]) :-
   shape(P, [4]), kind(P, float), permutation(P).

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
test(gather_needs_a_range, [timeout(10), throws(error(existence_error(elements, _), _))]) :-
   shape(Idx, [4]), shape(H, [3]),
   over([K:4], [H[Idx[K]] := 1]).

% Beyond affine: a remainder is hulled by its operation on exact hulls of its operands, and the
% whole posted once as terms in the extents.
test(hull_mod_relates_extents, [timeout(10), true(Lo == 3)]) :-
   shape(X, [M]),
   over([I:7], [_T[I] := X[I mod 3]]),
   range(M, [Lo, _]).
test(hull_quotient_is_exact, [timeout(10), true(Lo == 4)]) :-
   shape(X, [M]),
   over([I:7], [_T[I] := X[I // 2]]),
   range(M, [Lo, _]).
test(hull_quotient_symbolic, [timeout(10)]) :-
   shape(X, [N]), shape(Y, [H]),
   over([I:N], [Y[I // 2] := X[I]]),
   N = 8, range(H, [4, _]).
test(hull_nested_affine_is_exact, [timeout(10), true(Lo == 13)]) :-
   shape(X, [M]),
   over([I:4, J:2], [_T[I, J] := X[(2*I + J) mod 7 + 2*I]]),
   range(M, [Lo, _]).
test(hull_clamp_fits_anything, [timeout(10)]) :-
   shape(X, [N]),
   over([I:N], [_T[I] := X[min(I*3, N-1)]]).
test(hull_where_is_the_union, [timeout(10), true(Lo == 7)]) :-
   shape(X, [M]),
   over([I:3], [_T[I] := X[where(I < 1, I + 4, I)]]),
   range(M, [Lo, _]).
test(hull_symbolic_coefficient, [timeout(10), true(Lo == 6)]) :-
   shape(X, [N, M]),
   over([I:2, J:3], [T[I*M + J] := X[I, J]]),
   N = 2, M = 3, shape(T, [L]), range(L, [Lo, _]).
test(hull_xor_with_a_power_of_two, [timeout(10)]) :-
   power_of_two(N), shape(X, [N]), shape(S, [P]), elements(S, 0-(N-1)),
   over([Pi:P, I:N], [_T[Pi, I] := X[I xor S[Pi]]]).
test(hull_xor_needs_a_power_of_two, [timeout(10), throws(error(domain_error(power_of_two, _), _))]) :-
   shape(X, [N]),
   over([I:N], [_T[I] := X[I xor 1]]).
test(hull_and_needs_no_declaration, [timeout(10)]) :-
   shape(X, [N]), shape(S, [P]), elements(S, 0-(N-1)),
   over([Pi:P, I:N], [_T[Pi, I] := X[I /\ S[Pi]]]).
test(hull_shift, [timeout(10), true(Lo == 2)]) :-
   shape(X, [M]),
   over([I:8], [_T[I] := X[I >> 2]]),
   range(M, [Lo, _]).
test(hull_rejects_a_float_subscript, [timeout(10), throws(error(domain_error(kind, _), _))]) :-
   shape(X, [4]),
   over([I:4], [_T[I] := X[I / 2]]).
test(hull_rejects_a_float_operand, [timeout(10), throws(error(domain_error(kind, _), _))]) :-
   shape(X, [4]), shape(W, [4]), kind(W, float),
   over([I:4], [_T[I] := X[W[I] mod 2]]).
test(hull_quotient_needs_a_positive_divisor, [timeout(10), throws(error(domain_error(positive, _), _))]) :-
   shape(X, [N]), shape(D, [1]), elements(D, 0-3),
   over([I:N], [_T[I] := X[I // D[0]]]).
test(power_of_two_on_a_number, [timeout(10)]) :-
   power_of_two(8).
test(power_of_two_rejects_six, [timeout(10), throws(error(domain_error(power_of_two, 6), _))]) :-
   power_of_two(6).
test(power_of_two_binds_to_a_power, [timeout(10)]) :-
   power_of_two(N), shape(_X, [N]), N = 512.
test(power_of_two_refuses_six_later, [timeout(10)]) :-
   power_of_two(N), shape(_X, [N]),
   \+ catch(N = 6, error(domain_error(power_of_two, _), _), fail).
test(read_before_write, [timeout(10), fixme(needs_dependence_analysis),
                         throws(error(domain_error(written, _), _))]) :-
   over([T:8], [F[T] := F[T+1]]).

:- end_tests(core2).
