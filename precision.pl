:- module(precision, [
   post_precision/2,
   selection_precision/3,
   transfer_precision/3,
   choose_formats/3,
   sup_precision/2
]).

% The precision of an array encloses the absolute error of each of its
% elements: its upper bound is the guaranteed error.
% Each op posts a pointwise upper bound over the ranges and precisions of its
% arguments, so clpBNR re-tightens it whenever a range narrows or a format is
% chosen.
% A rounded result is bounded by Inherited*(1+U) + Rounding, where U is the
% unit roundoff of its format.

:- use_module(library(clpBNR)).
:- use_module(dtype, [dtype_info/5, unit_roundoff/2]).
:- use_module(array).

% post_precision(+Array0, -Array)
% Array is Array0, whose op was just pushed, with the precision of that op.
post_precision(M0, M), get_dict(op, M0, view(Parent)) =>
   M = M0.put(precision, Parent.precision).
% A scan has no error model either: the precision of its states, given.
post_precision(M0, M), get_dict(op, M0, scan(_, _, _, _, _, _, _)) =>
   M = M0.
post_precision(M0, M), get_dict(op, M0, solve(_, _)) =>
   % no error model: unknown
   M = M0.put(precision, P),
   P::real(0, inf).
post_precision(M0, M) =>
   inherited(M0.op, M0, Inherited),
   constrain(M0, Inherited, M).

% selection_precision(+M0, +Terms, -M)
% M is M0, a sum of Terms of which at most one is not 0, with its precision:
% the error of that term and a single rounding to the format of M, since
% adding 0 is exact in any order.
selection_precision(M0, Terms, M) :-
   M = M0.put(precision, P),
   P::real(0, inf),
   rounding_factor(M, U),
   { P =< Terms.precision*(1 + U) + U*abs(M.range) }.

% transfer_precision(+Source, +Copy0, -Copy)
% Copy is Copy0, a copy of Source in another buffer, with its precision.
transfer_precision(Src, Dst0, Dst) :-
   constrain(Dst0, Src.precision, Dst).

constrain(M0, Inherited, M) :-
   M = M0.put(precision, P),
   P::real(0, inf),
   rounding_factor(M, U),
   rounding(M.op, M, U, Rounding),
   { P =< Inherited*(1 + U) + Rounding }.

% Inherited error of an op, as a clpBNR expression.
inherited(true, _, I) => I = 0.
inherited(constant(_), _, I) => I = 0.
inherited(rand, _, I) => I = 0.
inherited(contiguous(A), _, I) => I = A.precision.
inherited(A+B, _, I) => I = A.precision + B.precision.
inherited(A*B, _, I) =>
   I = abs(B.range)*A.precision + abs(A.range)*B.precision
       + A.precision*B.precision.
% a comparison is either right or flipped: its error is at most 1
inherited(A<B, _, I) => I = (A.precision + B.precision > 0).
% a selection keeps the error of what it selects, unless a wrong condition
% selects the other one
inherited(where(C, A, B), _, I) =>
   I = max(A.precision, B.precision) + (C.precision > 0)*abs(A.range - B.range).
inherited(sin(A), _, I) => I = A.precision.
inherited(A**B, _, I) =>
   power_error(A, B, I).
% |log(x + e) - log(x)| =< e / (x - e), unbounded when the range reaches e
inherited(log(A), _, I) => I = A.precision / (A.range - A.precision).
inherited(float(A), _, I) => I = A.precision.
% rounding to an integer can move by one more
inherited(integer(A), _, I) => I = A.precision + (A.precision > 0).
inherited(reduce(+, Axes, A), _, I) =>
   array:reduce_count(A.shape(), Axes, N),
   I = N*A.precision.
% max is 1-Lipschitz
inherited(reduce(<, _, A), _, I) => I = A.precision.

% power_error(+A, +B, -I): I bounds the error of A**B from the errors of A
% and B. With an exact exponent or base, by the mean value theorem between
% the computed and the exact operand, which differ by its precision; a
% constant is taken as exact. The base of a
% real power is >= 0, as in its range.
% An integer exponent N: |N|*|x|**(N-1) grows with |x| when N > 1, and
% shrinks with |x| when N < 0, unbounded when the range reaches the error.
power_error(A, B, I), array:constant_value(B, Y), Y =:= truncate(Y) =>
   N is truncate(Y),
   integer_power_error(N, A, I).
% 0 < y < 1: |x**y - x'**y| =< |x - x'|**y
power_error(A, B, I), array:constant_value(B, Y), Y > 0, Y < 1 =>
   I = A.precision**Y.
power_error(A, B, I), array:constant_value(B, Y), Y > 1 =>
   I = Y*(max(A.range, 0) + A.precision)**(Y - 1)*A.precision.
power_error(A, B, I), array:constant_value(B, Y), Y < 0 =>
   I = abs(Y)*max(A.range - A.precision, 0)**(Y - 1)*A.precision.
% A base b > 0: |b**y - b**y'| =< |log(b)|*max(b**y, b**y')*|y - y'|
power_error(A, B, I), array:constant_value(A, Base), Base > 0 =>
   I = abs(log(Base))*max(Base**(B.range + B.precision),
                          Base**(B.range - B.precision))*B.precision.
% no error model for a power of two inexact operands: unknown
power_error(_, _, I) =>
   I::real(0, inf).

integer_power_error(0, _, I) =>
   I = 0.
integer_power_error(N, A, I), N > 0 =>
   I = N*(abs(A.range) + A.precision)**(N - 1)*A.precision.
integer_power_error(N, A, I) =>
   I = abs(N)*max(abs(A.range) - A.precision, 0)**(N - 1)*A.precision.

% Rounding error added by storing an op's result.
rounding(_, M, _, R), \+ get_dict(dtype, M, float) => R = 0.
rounding(rand, _, _, R) => R = 0.
rounding(reduce(<, _, _), _, _, R) => R = 0.
% A sum of N terms, in any order (any binary tree of additions), has an
% error of at most (N-1)*U*sum(|x_i|) =< (N-1)*U*N*|A|: kernels may reorder
% a sum, for example into SIMD lanes.
rounding(reduce(+, Axes, A), _, U, R) =>
   array:reduce_count(A.shape(), Axes, N),
   R = U*N*(N - 1)*abs(A.range).
rounding(_, M, U, R) => R = U*abs(M.range).

% The unit roundoff of a float array, bound when its format is.
% Only its upper bound matters: 0 lets a probe treat the array as exact.
rounding_factor(M, U), get_dict(dtype, M, float) =>
   device_float_formats(M.device, Formats),
   maplist(unit_roundoff, Formats, Us),
   max_list(Us, Hi),
   U::real(0, Hi),
   get_dict(format, M, Format),
   freeze(Format, bind_unit_roundoff(Format, U)).
rounding_factor(_, U) => U = 0.

% a constant only gets its device when combined with another array
device_float_formats(Device, Formats), var(Device) =>
   findall(F, (array:float_formats(_, Fs), member(F, Fs)), Formats).
device_float_formats(Device, Formats) =>
   array:float_formats(Device, Formats).

bind_unit_roundoff(Format, U) :-
   unit_roundoff(Format, U0),
   U = U0.

% The guaranteed error of an array.
sup_precision(A, S) :-
   get_dict(precision, A, P),
   sup(P, S).

sup(P, S), number(P) => S = P.
sup(P, S) => domain(P, D), arg(2, D, S).

% Formats
% =======

% choose_formats(+Schedule, +Outputs, +Tolerance)
% Bind the format of every array of Schedule, lowering float formats while the
% guaranteed error of every output stays within Tolerance.
choose_formats(Schedule, _, Tolerance), Tolerance == inf =>
   maplist(array:bind_default_format, Schedule).
choose_formats(Schedule, Outputs, Tolerance) =>
   format_candidates(Schedule, Candidates),
   maplist([c(_, F, _), F-float64]>>true, Candidates, Choice0),
   check_reachable(Schedule, Outputs, Tolerance, Candidates, Choice0),
   lower_formats(Schedule, Outputs, Tolerance, Candidates, Choice0, Choice),
   maplist(bind_choice, Choice),
   maplist(array:bind_default_format, Schedule).

% Float arrays whose format is not chosen yet and could be smaller, largest
% first, once per buffer (views share their parent's format).
format_candidates(Schedule, Candidates) :-
   convlist(format_candidate, Schedule, Candidates0),
   foldl(add_candidate, Candidates0, [], Candidates1),
   sort(1, @>=, Candidates1, Candidates).

format_candidate(M, c(Size, F, Fits)) :-
   get_dict(format, M, F),
   var(F),
   get_dict(dtype, M, float),
   get_dict(device, M, Device),
   nonvar(Device),
   array:range_min_max(M.range, Min, Max),
   array:float_formats(Device, Formats),
   include([Format]>>dtype_info(Format, float, Min, Max, []), Formats, Fits),
   Fits = [_, _ | _],
   Size = M.datasize.

add_candidate(c(_, F, _), Acc, Acc1), member(c(_, F1, _), Acc), F1 == F =>
   Acc1 = Acc.
add_candidate(C, Acc, Acc1) =>
   Acc1 = [C | Acc].

check_reachable(Schedule, Outputs, Tolerance, _, Choice),
      fits(Schedule, Outputs, Tolerance, Choice) =>
   true.
check_reachable(Schedule, Outputs, Tolerance, Candidates, Choice) =>
   precision_unreachable(Schedule, Outputs, Tolerance, Candidates, Choice).

% Lower one candidate by one format at a time, until no lowering fits anymore.
lower_formats(Schedule, Outputs, Tolerance, Candidates, Choice0, Choice) :-
   foldl(lower_one(Schedule, Outputs, Tolerance), Candidates,
         Choice0-false, Choice1-Changed),
   lower_again(Changed, Schedule, Outputs, Tolerance, Candidates, Choice1, Choice).

lower_again(true, Schedule, Outputs, Tolerance, Candidates, Choice1, Choice) =>
   lower_formats(Schedule, Outputs, Tolerance, Candidates, Choice1, Choice).
lower_again(false, _, _, _, _, Choice1, Choice) =>
   Choice = Choice1.

lower_one(Schedule, Outputs, Tolerance, c(_, F, Fits), Choice0-Changed0, Choice-Changed) :-
   choice_format(F, Choice0, Current),
   try_lower(Schedule, Outputs, Tolerance, F, Fits, Current,
             Choice0-Changed0, Choice-Changed).

try_lower(Schedule, Outputs, Tolerance, F, Fits, Current, Choice0-_, Choice-Changed),
      nextto(Lower, Current, Fits),
      set_choice(F, Lower, Choice0, Choice1),
      fits(Schedule, Outputs, Tolerance, Choice1) =>
   Choice = Choice1,
   Changed = true.
try_lower(_, _, _, _, _, _, Choice0-Changed0, Choice-Changed) =>
   Choice = Choice0,
   Changed = Changed0.

choice_format(F, Choice, Format) :-
   once(( member(F1-Format, Choice), F1 == F )).

set_choice(F, Format, Choice0, Choice) :-
   maplist(set_entry(F, Format), Choice0, Choice).

set_entry(F, Format, F1-_, Entry), F1 == F => Entry = F1-Format.
set_entry(_, _, Entry0, Entry) => Entry = Entry0.

bind_choice(F-Format) :-
   F = Format.

% Bind the formats tentatively and check every output, then undo it all.
fits(Schedule, Outputs, Tolerance, Choice) :-
   \+ \+ ( maplist(bind_choice, Choice),
           maplist(array:bind_default_format, Schedule),
           maplist(within(Tolerance), Outputs) ).

within(Tolerance, Out) :-
   sup_precision(Out, Sup),
   Sup =< Tolerance.

% Even float64 everywhere is not precise enough: report the bound reached, the
% part due to the inputs alone, and the array whose rounding costs the most.
precision_unreachable(Schedule, Outputs, Tolerance, Candidates, Choice) :-
   maplist([c(_, F, _), F]>>true, Candidates, Formats),
   probe_bound(Schedule, Outputs, Choice, [], Bound),
   probe_bound(Schedule, Outputs, [], Formats, Floor),
   maplist(probe_drop(Schedule, Outputs, Choice, Bound), Formats, Drops),
   pairs_keys_values(Pairs, Drops, Formats),
   main_contributor(Schedule, Pairs, Contributor),
   throw(error(precision_unreachable(Tolerance, Bound, Floor, Contributor), _)).

% Largest output error with the formats of Choice and the arrays of Exact
% treated as exact.
probe_bound(Schedule, Outputs, Choice, Exact, Bound) :-
   findall(B, once(( maplist(make_exact, Exact),
                     exclude(exact_choice(Exact), Choice, Choice1),
                     maplist(bind_choice, Choice1),
                     exclude(exact_array(Exact), Schedule, Schedule1),
                     maplist(array:bind_default_format, Schedule1),
                     maplist(sup_precision, Outputs, Sups),
                     max_list(Sups, B) )), [Bound]).

probe_drop(Schedule, Outputs, Choice, Bound, F, Drop) :-
   probe_bound(Schedule, Outputs, Choice, [F], B),
   Drop is Bound - B.

exact_choice(Exact, F-_) :- memberchk_eq(F, Exact).
exact_array(Exact, M) :- get_dict(format, M, F), memberchk_eq(F, Exact).

memberchk_eq(_, []) => fail.
memberchk_eq(X, [Y | _]), X == Y => true.
memberchk_eq(X, [_ | Ys]) => memberchk_eq(X, Ys).

% A format whose rounding factor is 0 rounds nothing.
make_exact(F) :-
   frozen(F, Goal),
   once(sub_term(bind_unit_roundoff(_, U), Goal)),
   U = 0.

main_contributor(_, [], Contributor) =>
   Contributor = none.
main_contributor(Schedule, Pairs, Contributor) =>
   max_member(_-F, Pairs),
   once(( member(M, Schedule), get_dict(format, M, F1), F1 == F )),
   op_summary(M.op, Op),
   Contributor = array(Op, M.shape()).

op_summary(Op, Summary), compound(Op) =>
   compound_name_arity(Op, Name, Arity),
   Summary = Name/Arity.
op_summary(Op, Summary) => Summary = Op.

:- multifile prolog:error_message//1.

prolog:error_message(precision_unreachable(Tolerance, Bound, Floor, Contributor)) -->
   [ 'Precision ~w is out of reach: float64 everywhere guarantees ~w, '-[Tolerance, Bound],
     '~w without rounding the computed arrays; largest rounding: ~p'-[Floor, Contributor] ].

:- begin_tests(precision).

test('product bound tightens with ranges and formats') :-
    A = array{}.fromlist([-100.0, 100.0], [device(c), precision(0.01)]),
    B = array{}.fromlist([-100.0, 100.0], [device(c), precision(0.01)]),
    C @= A * B,
    % format of C not chosen yet: up to float16 rounding
    sup_precision(C, S0),
    assertion((S0 > 6.88, S0 < 6.89)),
    array{range: RB} :< B,
    RB::real(-10, 10),
    sup_precision(C, S1),
    assertion((S1 > 1.58, S1 < 1.6)),
    C1 = C.realize(),
    sup_precision(C1, S2),
    assertion((S2 > 1.1, S2 < 1.1002)).

test('exact integer arithmetic has no error') :-
    A = array{}.fromlist([1, 2, 3]),
    B = array{}.fromlist([1, 2, 3], [device(c)]),
    C @= A * A + A,
    D @= B * B + B,
    sup_precision(C, SC),
    sup_precision(D, SD),
    SC =:= 0,
    SD =:= 0.

test('prolog float arithmetic rounds in float64') :-
    A = array{}.fromlist([1.0, 2.0]),
    C @= A + A,
    sup_precision(C, S),
    S > 0,
    S < 1.0e-15.

test('sum accumulates the error of its elements') :-
    A = array{}.fromlist([1.0, 2.0, 3.0], [precision(0.01)]),
    C = A.sum([0]),
    sup_precision(C, S),
    S >= 0.03,
    S < 0.0301.

test('comparison of inexact values may flip') :-
    A = array{}.fromlist([1.0, 2.0], [precision(0.01)]),
    B = array{}.fromlist([2.0, 1.0]),
    I = array{}.fromlist([1, 2]),
    C @= (A < B),
    D @= (I < 2),
    sup_precision(C, SC),
    sup_precision(D, SD),
    SC =:= 1,
    SD =:= 0.

test('a division is unbounded where the divisor reaches its error',
     [timeout(60)]) :-
    A = array{}.fromlist([-1.0, 1.0], [precision(0.01)]),
    B = array{}.fromlist([1.0, 2.0], [precision(0.01)]),
    C @= 1 / A,
    D @= 1 / B,
    sup_precision(C, SC),
    sup_precision(D, SD),
    SC =:= inf,
    % 0.01 / (1 - 0.01)**2
    SD > 0.0102,
    SD < 0.01021.

test('a square root has the error of its root', [timeout(60)]) :-
    A = array{}.fromlist([0.0, 4.0], [precision(0.01)]),
    C @= sqrt(A),
    sup_precision(C, S),
    S >= 0.1,
    S < 0.1001.

test('the error of exp grows with its exponent', [timeout(60)]) :-
    A = array{}.fromlist([0.0, 1.0], [precision(0.01)]),
    C @= exp(A),
    sup_precision(C, S),
    % e**1.01 * 0.01
    S > 0.02745,
    S < 0.02746.

test('a power of two inexact operands has an unknown error', [timeout(60)]) :-
    A = array{}.fromlist([1.0, 2.0], [precision(0.01)]),
    C @= A ** A,
    sup_precision(C, S),
    S =:= inf.

test('log reaching the error is unbounded') :-
    A = array{}.fromlist([0.0, 1.0], [precision(0.01)]),
    B = array{}.fromlist([1.0, 2.0], [precision(0.01)]),
    C @= log(A),
    D @= log(B),
    sup_precision(C, SC),
    sup_precision(D, SD),
    SC =:= inf,
    SD > 0.0101,
    SD < 0.0102.

test('solve has no error model') :-
    A = array{}.fromlist([[1.0, 0.0], [0.0, 2.0]]),
    B = array{}.fromlist([3.0, 4.0]),
    X @= solve(A, B),
    sup_precision(X, S),
    S =:= inf.

test('precision is kept when moving to prolog') :-
    A = array{}.fromlist([1.0, 2.0], [device(c), precision(0.01)]),
    C @= A + A,
    P = C.to(prolog),
    sup_precision(C, SC),
    sup_precision(P, SP),
    SC =:= SP.

product_plus(A, B, D, C) :-
    A = array{}.fromlist([37.0, 99.0, 3.0], [device(c)]),
    B = array{}.fromlist([12.0, 98.0, 7.0], [device(c)]),
    D @= A * B,
    C @= D + A.

formats(Arrays, Formats) :-
    maplist([A, F]>>(array{format: F} :< A), Arrays, Formats).

test('no tolerance keeps float64') :-
    product_plus(_, _, D, C),
    _ = C.realize(),
    formats([D, C], [float64, float64]).

% D is inlined in C's kernel, which computes it in the float64 of its inputs
test('tolerance lowers formats',
     [forall(member(T-Formats, [20-[float64, float16],
                                6-[float64, float16],
                                1-[float64, float32]]))]) :-
    product_plus(_, _, D, C),
    C1 = C.realize([precision(T)]),
    formats([D, C1], Formats),
    sup_precision(C1, S),
    S =< T.

test('unreachable tolerance',
     [throws(error(precision_unreachable(1.0e-12, _, _, array((+)/2, [3])), _))]) :-
    product_plus(_, _, _, C),
    _ = C.realize([precision(1.0e-12)]).

test('tolist passes the tolerance') :-
    product_plus(_, _, _, C),
    C.tolist([precision(20)]) == [481.0, 9800.0, 24.0].

% exact integers on prolog against lowered float formats on c
test('lowered results stay within the guaranteed error') :-
    set_random(seed(42)),
    length(As, 64),
    length(Bs, 64),
    maplist([X]>>random_between(0, 100, X), As),
    maplist([X]>>random_between(0, 100, X), Bs),
    maplist([X, Y]>>(Y is float(X)), As, FAs),
    maplist([X, Y]>>(Y is float(X)), Bs, FBs),
    maplist([A, B, E]>>(E is A*B + A), As, Bs, Exact),
    FA = array{}.fromlist(FAs, [device(c)]),
    FB = array{}.fromlist(FBs, [device(c)]),
    D @= FA * FB,
    C @= D + FA,
    C1 = C.realize([precision(20)]),
    formats([D, C1], [float64, float16]),
    sup_precision(C1, S),
    Values = C1.tolist(),
    forall(nth1(I, Values, V),
           (  nth1(I, Exact, E),
              assertion(abs(V - E) =< S)
           )).

% the c kernel reorders the sum into SIMD lanes
test('a reordered sum stays within the guaranteed error') :-
    set_random(seed(7)),
    length(Xs, 100000),
    maplist([X]>>(X is random_float), Xs),
    foldl([X, S0, S1]>>(S1 is S0 + rational(X)), Xs, 0, Exact),
    A = array{}.fromlist(Xs, [device(c)]),
    C = A.sum().realize(),
    sup_precision(C, Bound),
    Value = C.tolist(),
    abs(rational(Value) - Exact) =< Bound.

:- end_tests(precision).
