:- module(grad2, [partial/3, vjp/4, grad/3, jvp/5]).
:- use_module(library(clpBNR)).
:- use_module(library(apply)).
:- use_module(library(lists)).
:- use_module(library(error)).
:- use_module(core2).
:- use_module(compile2, [program/2]).

/** <module> Differentiation of a program of boxes

A program is differentiated as source: new boxes, over new names, hang on the names of the
program, and the derivative is a program like any other, compiled and run by compile2. No
tape, no runtime graph: the forward values the derivative needs are read from the names that
hold them, so a value that is overwritten before the program ends cannot be used, see below.

The derivative of an equation A[Ts] := V is in its partials: partial(V, R, D) is dV/dR for a
read R of V, a place N[Es] or a rank-0 name, as a value, by the rules of the primitives:
where/3 differentiates its branches under its condition, max and min select, a comparison,
an integer operation and bits/1 are constant. A read of an int or bool name, a subscript, is
never differentiated. An input or a written name is active when it is a float on a path
from the seeds; the derivative of an inactive read is 0 and no name is made for it.

Reverse mode, vjp/4 and grad/3: every active name N but the output gets an adjoint Nbar of
its shape, initialised to 0; the output's adjoint is the seed, an input of the derivative
program, or 1 for a rank-0 loss. The boxes are walked last to first, their equations last
to first. The adjoint of A[Ts] := V adds Abar[Ts] * dV/dR to Nbar[Es] for each active read
R = N[Es] of V, a scatter-add the compiler folds by + or runs atomically; then, when V reads
A[Ts] itself with a partial D other than 1, scales Abar[Ts] by D, and when V does not read
A[Ts], the write overwrote a value, and Abar[Ts] is reset to 0 for the readers of that value.
A fold A[Ts] := A[Ts] + E thus costs nothing on Abar. A fold by max or min reads the final
value: the read E that equals A[Ts] at the end gets the adjoint, where(E =:= A[Ts], ...);
the fold must start from a constant.

A box of plain equations, each a pure write at targets covering every axis or a fold of its
own place, with no carried axis, is distributed: each read's accumulation is a box of its
own over the box's axes in their order, so that the scheduler sees a matmul's two adjoints
as two matmuls and a reduction's adjoint as a broadcast over the same rows. The reset of
Abar[Ts] cannot be a box of its own: program/2 orders a reader of a name after every box
writing it, so a write after the reads must sit in the same box as the reads; an equation
whose adjoint resets or scales Abar[Ts] is one box of all its accumulations, in order.
Any other box is reversed whole: every axis backwards, the index I replaced by E-1-I, its
structure kept, every overwrite reset. That covers a recurrence, an axis along which a
name is accessed at two places, whose derivative is a recurrence the other way, each step
needing every term; a box with inner boxes; and a last-writer-wins write.

Forward mode, jvp/5: every active name N gets a tangent dN of shape [ND | Shape], ND
directions at once, so that the Jacobian of a model of N inputs is one program: the tangent
of the input seeded with the identity, dX[Dr, J] := where(J =:= Dr, 1.0, 0.0), and the
tangent of each output read as its Jacobian, direction first. Several outputs share one
tangent program, as an EKF's transition and observation share the model's terms. The tangent of A[Ts] := V is
dA[Dr | Ts] := sum of dV/dR * dN[Dr | Es] over the active reads, the self-read of a fold
keeping dA[Dr | Ts] as a term, a max or min fold selecting where(E =:= A[Ts], dE, dA). The
tangent boxes of a box come after it, the forward values final; a distributed box gives a
box per term, a fold's tangent a fold, the others a write then accumulations.

What is not available: a partial may read a name written by a box after the one it belongs
to, or by the same box not at distinct places (a fold by *, an in-place update under a
sequential axis, a local accumulator of a nested box), and that value is gone when the
derivative runs. Such a read is domain_error(available, Name). The next step is to keep such
a value by giving its name the sequential axes along which it is overwritten (a tape by
expansion), which rewrites the forward program and is not done here; a fold by * could also
be read as its final value divided by the operand.

Partials are simplified as they are built: 0 and 1 drop out, numbers fold, and a where of
equal branches is the branch; nothing else, so dV/dR of exp(X) is exp(X) read again and
recomputed by the adjoint box, which is the compiler's business to fuse or not.
*/

% partial(+V, +R, -D): D is dV/dR, R a read of V, as a value.
partial(V, R, D), V == R => D = 1.
partial(V, _, D), var(V) => D = 0.
partial(N, _, D), number(N) => D = 0.
partial(P, _, D), core2:place(P, _, _) => D = 0.
partial(A + B, R, D) => partial(A, R, Da), partial(B, R, Db), add(Da, Db, D).
partial(A - B, R, D) => partial(A, R, Da), partial(B, R, Db), sub(Da, Db, D).
partial(-A, R, D) => partial(A, R, Da), neg(Da, D).
partial(A * B, R, D) =>
   partial(A, R, Da), partial(B, R, Db),
   mul(Da, B, P1), mul(A, Db, P2), add(P1, P2, D).
partial(A / B, R, D) =>
   partial(A, R, Da), partial(B, R, Db),
   quo(Da, B, Q1),
   mul(A, Db, P), quo(P, B * B, Q2),
   sub(Q1, Q2, D).
partial(exp(A), R, D) => partial(A, R, Da), mul(Da, exp(A), D).
partial(log(A), R, D) => partial(A, R, Da), quo(Da, A, D).
partial(sqrt(A), R, D) => partial(A, R, Da), quo(Da, 2 * sqrt(A), D).
partial(max(A, B), R, D) => partial(A, R, Da), partial(B, R, Db), choose(B < A, Da, Db, D).
partial(min(A, B), R, D) => partial(A, R, Da), partial(B, R, Db), choose(A < B, Da, Db, D).
partial(where(C, T, E), R, D) => partial(T, R, Dt), partial(E, R, De), choose(C, Dt, De, D).
partial(E, _, D), E =.. [Op | _], memberchk(Op, [<, =<, =:=, bits]) => D = 0.
partial(E, _, D), E =.. [Op | _], core2:int_op(Op) => D = 0.
partial(E, _, _) => type_error(value, E).

zero(X) :- number(X), X =:= 0.
one(X) :- number(X), X =:= 1.

add(A, B, S), zero(A) => S = B.
add(A, B, S), zero(B) => S = A.
add(A, B, S), number(A), number(B) => S is A + B.
add(A, B, S) => S = A + B.

sub(A, B, S), zero(B) => S = A.
sub(A, B, S), zero(A) => neg(B, S).
sub(A, B, S), number(A), number(B) => S is A - B.
sub(A, B, S) => S = A - B.

neg(A, S), number(A) => S is -A.
neg(A, S) => S = -A.

mul(A, B, P), ( zero(A) ; zero(B) ) => P = 0.
mul(A, B, P), one(A) => P = B.
mul(A, B, P), one(B) => P = A.
mul(A, B, P), number(A), number(B) => P is A * B.
mul(A, B, P) => P = A * B.

quo(A, _, Q), zero(A) => Q = 0.
quo(A, B, Q), one(B) => Q = A.
quo(A, B, Q), number(A), number(B) => Q is A / B.
quo(A, B, Q) => Q = A / B.

choose(_, T, E, D), T == E => D = T.
choose(C, T, E, D) => D = where(C, T, E).

total([T], S) => S = T.
total([T | Ts], S) => total(Ts, S0), add(T, S0, S).

% reads(+V, -Rs): the reads of V, places and rank-0 names, each once, those in subscripts too.
reads(V, Rs) :-
   reads(V, Rs0, []),
   dedupe(Rs0, Rs).

reads(V, Rs0, Rs), var(V), is_name(V) => Rs0 = [V | Rs].
reads(V, Rs0, Rs), var(V) => Rs0 = Rs.
reads(N, Rs0, Rs), atomic(N) => Rs0 = Rs.
reads(P, Rs0, Rs), core2:place(P, _, Es) => Rs0 = [P | Rs1], foldl(reads, Es, Rs1, Rs).
reads(E, Rs0, Rs), compound(E) => E =.. [_ | As], foldl(reads, As, Rs0, Rs).

dedupe([], []).
dedupe([R | Rs0], [R | Rs]) :-
   exclude(==(R), Rs0, Rs1),
   dedupe(Rs1, Rs).

read_name(R, N), var(R) => N = R.
read_name(R, N) => core2:place(R, N, _).

read_subs(R, Es), var(R) => Es = [].
read_subs(R, Es) => core2:place(R, _, Es).

place_of(N, [], P) => P = N.
place_of(N, Es, P) => P = [](Es, N).

is_name(V) :-
   get_attr(V, core2, _).

names(Term, Names) :-
   term_variables(Term, Vs),
   include(is_name, Vs, Names).

in_names(Names, N) :-
   member(M, Names),
   M == N,
   !.

lookup(Map, N, X) :-
   member(M-X0, Map),
   M == N,
   !,
   X = X0.

% floatable(+N): the kind of N is, or may still be, float.
floatable(N) :-
   core2:name_kind(N, K),
   (  integer(K)
   -> K =:= 2
   ;  range(K, [_, Hi]), Hi =:= 2
   ).

seed_name(N) :-
   must_be(name, N),
   (  floatable(N)
   -> true
   ;  domain_error(kind, N)
   ).

% Equations with their scope
% ==========================

% equations(+Box, -Eqs): the equations of Box in order, eq(Scope, P := V), Scope the axes
% around each, innermost first.
equations(Box, Eqs) :-
   box_eqs([], Box, Eqs, []).

box_eqs(Scope, over(Axes, Items), Eqs0, Eqs) :-
   append(Axes, Scope, Scope1),
   foldl(item_eqs(Scope1), Items, Eqs0, Eqs).

item_eqs(Scope, over(Axes, Items), Eqs0, Eqs) => box_eqs(Scope, over(Axes, Items), Eqs0, Eqs).
item_eqs(Scope, P := V, Eqs0, Eqs) => Eqs0 = [eq(Scope, P := V) | Eqs].

target(eq(_, P := _), A) :-
   core2:place(P, A, _).

% injective(+Eq): the targets of the equation cover every axis in its scope: each point of
% the scope writes its own place, so no write of the box overwrites another.
injective(eq(Scope, P := _)) :-
   core2:place(P, _, Ts),
   forall(member(D:_, Scope), ( member(T, Ts), compile2:covers(Scope, T, D) )).

% eq_reads(+Eq, -Rs): the reads of the equation, in its value and in its targets.
eq_reads(eq(_, P := V), Rs) :-
   core2:place(P, _, Ts),
   reads(f(Ts, V), Rs).

% active(+Seeds, +Boxes, -Active): the floatable names of Boxes on a path from Seeds: a
% target is active when a read of its value is, to a fixpoint.
active(Seeds, Boxes, Active) :-
   foldl(equations_of, Boxes, Eqs, []),
   closure(Eqs, Seeds, Active).

equations_of(Box, Eqs0, Eqs) :-
   box_eqs([], Box, Eqs0, Eqs).

closure(Eqs, Active0, Active) :-
   foldl(activate, Eqs, Active0, Active1),
   (  same_length(Active0, Active1)
   -> Active = Active1
   ;  closure(Eqs, Active1, Active)
   ).

activate(eq(_, P := V), Active0, Active) :-
   core2:place(P, A, _),
   (  \+ in_names(Active0, A),
      floatable(A),
      reads(V, Rs), member(R, Rs), read_name(R, N), in_names(Active0, N)
   -> Active = [A | Active0]
   ;  Active = Active0
   ).

% Availability
% ============

% infos(+Boxes, -Infos): for each box, info(Written, Injective, Read, Eqs): the names it
% writes, those it writes by one injective equation, the names it reads, and its equations.
infos(Boxes, Infos) :-
   maplist(info, Boxes, Infos).

info(Box, info(Written, Injective, Read, Eqs)) :-
   equations(Box, Eqs),
   maplist(target, Eqs, Targets0),
   dedupe(Targets0, Written),
   include(injective, Eqs, Injs),
   maplist(target, Injs, Ts),
   include(written_once(Targets0), Ts, Injective),
   maplist(eq_reads, Eqs, Rss),
   append(Rss, Rs),
   maplist(read_name, Rs, Ns0),
   dedupe(Ns0, Read).

written_once(Targets, A) :-
   include(==(A), Targets, [_]).

writes(info(W, _, _, _), A) :- in_names(W, A).
reads_name(info(_, _, R, _), A) :- in_names(R, A).

% available(+Infos, +I, +Allowed, +Term): every name Term reads holds, when the derivative
% runs, the value box I read: its writers are before I, or I itself at distinct places; a
% name of Allowed may be written by I anyhow, its final value being the one wanted, and
% must not be written after.
available(Infos, I, Allowed, Term) :-
   names(Term, Ns),
   (  member(N, Ns), \+ final(Infos, I, Allowed, N)
   -> domain_error(available, N)
   ;  true
   ).

final(Infos, I, Allowed, N) :-
   forall(nth0(J, Infos, info(W, Inj, _, _)),
          (  \+ in_names(W, N)
          ;  J < I
          ;  J =:= I, ( in_names(Inj, N) ; in_names(Allowed, N) ) )).

% constant_inits(+Infos, +I, +A): the writes of A before box I are numbers: the fold of
% box I starts from a constant.
constant_inits(Infos, I, A) :-
   forall(( nth0(J, Infos, info(_, _, _, Eqs)), J < I,
            member(eq(_, P := V), Eqs), core2:place(P, A1, _), A1 == A ),
          number(V)),
   !.
constant_inits(_, _, A) :-
   domain_error(constant_init, A).

% max_fold(+Eq, -E): the equation folds its own place by max or min with E, which does not
% read the name.
max_fold(P := V, E) :-
   compound(V),
   V =.. [Op, X, Y],
   memberchk(Op, [max, min]),
   (  X == P
   -> E = Y
   ;  Y == P, E = X
   ),
   core2:place(P, A, _),
   reads(E, Rs),
   \+ ( member(R, Rs), read_name(R, N), N == A ).

% Boxes
% =====

% distributable(+Box): a box of plain equations, each injective or a fold of its own place,
% no name written twice, no axis carried: the adjoint or the tangent of each equation can be
% boxes of its own. Along a carried axis the derivative is a recurrence too, each step of
% which needs every term: it stays one box.
distributable(over(Axes, Items)) :-
   \+ ( member(over(_, _), Items) ),
   carried(over(Axes, Items), []),
   equations(over(Axes, Items), Eqs),
   maplist(target, Eqs, Targets),
   dedupe(Targets, Written), same_length(Targets, Written),
   forall(member(Eq, Eqs), ( injective(Eq) ; own_fold(Eq) )).

own_fold(eq(_, P := V)) :-
   core2:place(P, A, Ts),
   compile2:accesses(P := V, A, Ss),
   Ss = [_, _ | _],
   forall(member(S, Ss), S == Ts).

% carried(+Box, -Is): the indices of the box's axes along which a written name is accessed
% at two different places: the adjoint runs them backwards.
carried(over(Axes, Items), Is) :-
   core2:writes(over(Axes, Items), Written),
   maplist(arg(1), Axes, Is0),
   include(carried_axis(over(Axes, Items), Written), Is0, Is).

carried_axis(Box, Written, I) :-
   member(A, Written),
   compile2:accesses(Box, A, Ss),
   member(S1, Ss), member(S2, Ss),
   nth0(P, S1, X), nth0(P, S2, Y), X \== Y,
   ( compile2:mentions(X, I) ; compile2:mentions(Y, I) ),
   !.

% fresh_box(+Rev, +Axes0, +Items0, -Axes, -Items): the box with new indices, those of Rev,
% or all of them when Rev is all, running backwards: I replaced by E-1-I in the equations.
fresh_box(Rev, Axes0, Items0, Axes, Items) :-
   index_map(Rev, over(Axes0, Items0), Map, []),
   rename(Map, over(Axes0, Items0), over(Axes, Items)).

index_map(Rev, over(Axes, Items), Map0, Map) :-
   foldl(axis_map(Rev), Axes, Map0, Map1),
   foldl(index_map(Rev), Items, Map1, Map).
index_map(_, _ := _, Map, Map).

axis_map(Rev, I:E, [I-I1-S | Map], Map) :-
   (  reversed(Rev, I)
   -> S = E - 1 - I1
   ;  S = I1
   ).

reversed(all, _) => true.
reversed(Is, I) => member(J, Is), J == I, !.

rename(Map, over(Axes0, Items0), T) =>
   maplist(rename_axis(Map), Axes0, Axes),
   maplist(rename(Map), Items0, Items),
   T = over(Axes, Items).
rename(Map, T0, T), var(T0), member(I-_-S, Map), I == T0 => T = S.
rename(_, T0, T), var(T0) => T = T0.
rename(Map, T0, T), compound(T0) =>
   T0 =.. [F | As0],
   maplist(rename(Map), As0, As),
   T =.. [F | As].
rename(_, T0, T) => T = T0.

rename_axis(Map, I:E, I1:E) :-
   member(J-I1-_, Map), J == I, !.

zero_box(N) :-
   shape(N, Shape),
   maplist(axis_of, Shape, Axes, Is),
   place_of(N, Is, P),
   over(Axes, [P := 0.0]).

axis_of(E, I:E, I).

% Reverse mode
% ============

% vjp(+Out, +Params, -OutBar, -Grads): the program of Out extended with its backward: OutBar
% an input of the shape of Out, the cotangent, and Grads names of the shapes of Params
% holding OutBar times the Jacobian of Out in Params.
vjp(Out, Params, OutBar, Grads) :-
   must_be(name, Out),
   must_be(list, Params),
   maplist(seed_name, Params),
   program(Out, Boxes),
   active(Params, Boxes, Active),
   shape(Out, Shape), shape(OutBar, Shape), kind(OutBar, float),
   foldl(adjoint_name(Out, OutBar), Active, [Out-OutBar], Map),
   infos(Boxes, Infos),
   length(Boxes, L), Last is L - 1,
   reverse(Boxes, Rev),
   foldl(adjoint_box(Infos, Map), Rev, Last, _),
   maplist(lookup(Map), Params, Grads).

adjoint_name(Out, _, N, Map, Map1), N == Out => Map1 = Map.
adjoint_name(_, _, N, Map, Map1) =>
   shape(N, Shape), shape(Nbar, Shape), zero_box(Nbar),
   Map1 = [N-Nbar | Map].

% grad(+Loss, +Params, -Grads): the gradients of the rank-0 name Loss in Params.
grad(Loss, Params, Grads) :-
   must_be(name, Loss),
   (  shape(Loss, [])
   -> true
   ;  shape(Loss, Shape), domain_error(rank(0), Shape)
   ),
   vjp(Loss, Params, LossBar, Grads),
   over([], [LossBar := 1.0]).

% adjoint_box(+Infos, +Map, +Box, +I, -I1): the adjoint boxes of Box, the I-th: distributed
% when it can be, else one box, every axis backwards, every overwrite reset.
adjoint_box(Infos, Map, Box, I, I1) :-
   I1 is I - 1,
   Box = over(Axes, Items),
   (  distributable(Box)
   -> reverse(Items, RItems),
      maplist(adjoint_eq_boxes(Infos, Map, I, Box, Axes), RItems)
   ;  adjoint_items(Infos, Map, I, Box, always, Items, AItems),
      (  AItems == []
      -> true
      ;  fresh_box(all, Axes, AItems, Axes1, AItems1),
         over(Axes1, AItems1)
      )
   ).

adjoint_eq_boxes(Infos, Map, I, Box, Axes, Eq) :-
   eq_adjoint(Infos, Map, I, Box, needed, Eq, Items, InPlace),
   (  Items == []
   -> true
   ;  InPlace == true
   -> fresh_box([], Axes, Items, Axes1, Items1), over(Axes1, Items1)
   ;  maplist(adjoint_box_of(Axes), Items)
   ).

adjoint_box_of(Axes, Item) :-
   fresh_box([], Axes, [Item], Axes1, Items1),
   over(Axes1, Items1).

% adjoint_items(+Infos, +Map, +I, +Box, +Zero, +Items, -AItems): the adjoint of Items, last
% to first, an inner box an inner box.
adjoint_items(Infos, Map, I, Box, Zero, Items, AItems) :-
   reverse(Items, RItems),
   foldl(adjoint_item(Infos, Map, I, Box, Zero), RItems, AItems, []).

adjoint_item(Infos, Map, I, Box, Zero, over(Axes, Inner), AItems0, AItems) =>
   adjoint_items(Infos, Map, I, Box, Zero, Inner, AInner),
   (  AInner == []
   -> AItems0 = AItems
   ;  AItems0 = [over(Axes, AInner) | AItems]
   ).
adjoint_item(Infos, Map, I, Box, Zero, Eq, AItems0, AItems) =>
   eq_adjoint(Infos, Map, I, Box, Zero, Eq, Items, _),
   append(Items, AItems, AItems0).

% eq_adjoint(+Infos, +Map, +I, +Box, +Zero, +Eq, -Items, -InPlace): the adjoint equations of
% Eq, in order: an accumulation per active read, then the update of the target's own
% adjoint, scaled by the partial of its self-read, or reset after an overwrite: always, or
% when needed, a value of the place having been read before. InPlace is true when there is
% such an update.
eq_adjoint(Infos, Map, I, Box, Zero, P := V, Items, InPlace) :-
   core2:place(P, A, Ts),
   (  lookup(Map, A, Abar)
   -> place_of(Abar, Ts, AbarP),
      (  max_fold(P := V, E)
      -> constant_inits(Infos, I, A),
         reads(E, Rs),
         foldl(max_item(Infos, Map, I, A, Ts, E, AbarP), Rs, Items0, []),
         Items = Items0, InPlace = false
      ;  reads(V, Rs),
         partition(==(P), Rs, Selfs, Others),
         foldl(read_item(Infos, Map, I, V, Ts, AbarP), Others, Items0, Items1),
         (  Selfs = [Self]
         -> partial(V, Self, D),
            (  one(D)
            -> Items1 = [], InPlace = false
            ;  available(Infos, I, [], D),
               mul(AbarP, D, Scaled),
               Items1 = [AbarP := Scaled], InPlace = true
            )
         ;  Zero == always
         -> Items1 = [AbarP := 0.0], InPlace = true
         ;  needs_zero(Infos, I, Box, A, Ts)
         -> Items1 = [AbarP := 0.0], InPlace = true
         ;  Items1 = [], InPlace = false
         ),
         Items = Items0
      )
   ;  Items = [], InPlace = false
   ).

read_item(Infos, Map, I, V, Ts, AbarP, R, Items0, Items) :-
   read_name(R, N),
   (  lookup(Map, N, Nbar),
      partial(V, R, D),
      \+ zero(D)
   -> read_subs(R, Es),
      available(Infos, I, [], f(Ts, Es, D)),
      place_of(Nbar, Es, NbarP),
      mul(AbarP, D, T),
      Items0 = [NbarP := NbarP + T | Items]
   ;  Items0 = Items
   ).

max_item(Infos, Map, I, A, Ts, E, AbarP, R, Items0, Items) :-
   read_name(R, N),
   (  lookup(Map, N, Nbar),
      partial(E, R, D),
      \+ zero(D)
   -> read_subs(R, Es),
      available(Infos, I, [A], f(Ts, Es, D, E)),
      place_of(Nbar, Es, NbarP),
      place_of(A, Ts, AP),
      mul(AbarP, D, T),
      Items0 = [NbarP := NbarP + where(E =:= AP, T, 0.0) | Items]
   ;  Items0 = Items
   ).

% needs_zero(+Infos, +I, +Box, +A, +Ts): a value of A[Ts] overwritten by box I was read: by a
% box before I, or by box I at another place.
needs_zero(Infos, I, Box, A, Ts) :-
   (  nth0(J, Infos, Info), J < I, reads_name(Info, A)
   -> true
   ;  equations(Box, Eqs),
      member(Eq, Eqs), eq_reads(Eq, Rs),
      member(R, Rs), read_name(R, N), N == A, read_subs(R, Es), Es \== Ts
   -> true
   ).

% Forward mode
% ============

% jvp(+Outs, +Ins, +ND, -Tangents, -OutTs): the program of the names Outs extended with its
% tangent along ND directions: Tangents inputs of the shapes of Ins with a leading axis of ND,
% OutTs names of the shapes of Outs with the same, the Jacobian of each Out in Ins applied to
% Tangents. A tangent of Tangents may be written by the caller instead, as the identity for a
% whole Jacobian.
jvp(Outs, Ins, ND, Tangents, OutTs) :-
   must_be(list(name), Outs),
   must_be(list, Ins),
   maplist(seed_name, Ins),
   must_be(extent, ND),
   programs(Outs, Boxes),
   active(Ins, Boxes, Active),
   foldl(tangent_name(ND), Active, [], Map),
   infos(Boxes, Infos),
   foldl(tangent_box(Infos, Map, ND), Boxes, 0, _),
   maplist(lookup(Map), Ins, Tangents),
   maplist(out_tangent(Map, ND), Outs, OutTs).

out_tangent(Map, _, Out, OutT), lookup(Map, Out, OutT0) => OutT = OutT0.
out_tangent(_, ND, Out, OutT) => shape(Out, Shape), shape(OutT, [ND | Shape]), zero_box(OutT).

% programs(+Outs, -Boxes): the boxes the names Outs depend on, each after its dependencies:
% the program of each in turn, less the boxes already taken.
programs(Outs, Boxes) :-
   foldl(add_program, Outs, [], Rev),
   reverse(Rev, Boxes).

add_program(Out, Rev0, Rev) :-
   program(Out, Bs),
   foldl(add_box, Bs, Rev0, Rev).

add_box(B, Rev0, Rev), compile2:in_list(Rev0, B) => Rev = Rev0.
add_box(B, Rev0, Rev) => Rev = [B | Rev0].

tangent_name(ND, N, Map, [N-DN | Map]) :-
   shape(N, Shape),
   shape(DN, [ND | Shape]),
   (  core2:written(N)
   -> true
   ;  kind(DN, float)
   ).

% tangent_box(+Infos, +Map, +ND, +Box, +I, -I1): the tangent boxes of Box, the I-th, after
% it: a box per term when distributed, else one box of the structure of Box.
tangent_box(Infos, Map, ND, Box, I, I1) :-
   I1 is I + 1,
   Box = over(Axes, Items),
   (  distributable(Box)
   -> maplist(tangent_eq_boxes(Infos, Map, I, ND, Axes), Items)
   ;  foldl(tangent_item(Infos, Map, I, Dr), Items, TItems, []),
      (  TItems == []
      -> true
      ;  fresh_box([], [Dr:ND | Axes], TItems, Axes1, TItems1),
         over(Axes1, TItems1)
      )
   ).

tangent_eq_boxes(Infos, Map, I, ND, Axes, Eq) :-
   eq_tangent(Infos, Map, I, Dr, Eq, Boxes),
   maplist(tangent_box_of(Dr, ND, Axes), Boxes).

tangent_box_of(Dr, ND, Axes, Items) :-
   fresh_box([], [Dr:ND | Axes], Items, Axes1, Items1),
   over(Axes1, Items1).

tangent_item(Infos, Map, I, Dr, over(Axes, Inner), TItems0, TItems) =>
   foldl(tangent_item(Infos, Map, I, Dr), Inner, TInner, []),
   (  TInner == []
   -> TItems0 = TItems
   ;  TItems0 = [over(Axes, TInner) | TItems]
   ).
tangent_item(Infos, Map, I, Dr, Eq, TItems0, TItems) =>
   eq_tangent(Infos, Map, I, Dr, Eq, Boxes),
   append(Boxes, Items),
   append(Items, TItems, TItems0).

% eq_tangent(+Infos, +Map, +I, +Dr, +Eq, -Boxes): the tangent equations of Eq, as lists, each
% a box when distributed, their concatenation in order otherwise.
eq_tangent(Infos, Map, I, Dr, P := V, Boxes) :-
   core2:place(P, A, Ts),
   (  lookup(Map, A, DA)
   -> DAP = []([Dr | Ts], DA),
      (  max_fold(P := V, E)
      -> constant_inits(Infos, I, A),
         reads(E, Rs),
         foldl(tangent_term(Infos, Map, I, Dr, E, Ts, [A]), Rs, Terms, []),
         (  Terms == []
         -> Boxes = []
         ;  total(Terms, S),
            available(Infos, I, [A], E),
            Boxes = [[DAP := where(E =:= P, S, DAP)]]
         )
      ;  reads(V, Rs),
         partition(==(P), Rs, Selfs, Others),
         foldl(tangent_term(Infos, Map, I, Dr, V, Ts, []), Others, Terms, []),
         (  Selfs = [Self]
         -> partial(V, Self, D),
            (  one(D)
            -> maplist(accumulation(DAP), Terms, Boxes)
            ;  available(Infos, I, [], D),
               mul(D, DAP, T0),
               total([T0 | Terms], S),
               Boxes = [[DAP := S]]
            )
         ;  Terms == []
         -> Boxes = [[DAP := 0.0]]
         ;  Terms = [T1 | Tk],
            maplist(accumulation(DAP), Tk, Boxes1),
            Boxes = [[DAP := T1] | Boxes1]
         )
      )
   ;  Boxes = []
   ).

tangent_term(Infos, Map, I, Dr, V, Ts, Allowed, R, Terms0, Terms) :-
   read_name(R, N),
   (  lookup(Map, N, DN),
      partial(V, R, D),
      \+ zero(D)
   -> read_subs(R, Es),
      available(Infos, I, Allowed, f(Ts, Es, D)),
      mul(D, []([Dr | Es], DN), T),
      Terms0 = [T | Terms]
   ;  Terms0 = Terms
   ).

accumulation(DAP, T, [DAP := DAP + T]).
