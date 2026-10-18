:- module(precision, [
   post_precision/2,
   transfer_precision/3,
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
:- use_module(dtype, [unit_roundoff/2]).
:- use_module(array).

% post_precision(+Array0, -Array)
% Array is Array0, whose op was just pushed, with the precision of that op.
post_precision(M0, M), get_dict(op, M0, view(Parent)) =>
   M = M0.put(precision, Parent.precision).
post_precision(M0, M), get_dict(op, M0, solve(_, _)) =>
   % no error model: unknown
   M = M0.put(precision, P),
   P::real(0, inf).
post_precision(M0, M) =>
   inherited(M0.op, M0, Inherited),
   constrain(M0, Inherited, M).

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
inherited(sin(A), _, I) => I = A.precision.
% |sqrt(x) - sqrt(y)| =< sqrt(|x - y|)
inherited(sqrt(A), _, I) => I = sqrt(A.precision).
% |log(x + e) - log(x)| =< e / (x - e), unbounded when the range reaches e
inherited(log(A), _, I) => I = A.precision / (A.range - A.precision).
inherited(float(A), _, I) => I = A.precision.
% rounding to an integer can move by one more
inherited(integer(A), _, I) => I = A.precision + (A.precision > 0).
inherited(reduce(+, _, A), M, I) =>
   reduce_size(A, M, N),
   I = N*A.precision.
% max is 1-Lipschitz
inherited(reduce(<, _, A), _, I) => I = A.precision.

% Rounding error added by storing an op's result.
rounding(_, M, _, R), \+ get_dict(dtype, M, float) => R = 0.
rounding(rand, _, _, R) => R = 0.
rounding(reduce(<, _, _), _, _, R) => R = 0.
% naive summation: the k-th partial sum is rounded once
rounding(reduce(+, _, A), M, U, R) =>
   reduce_size(A, M, N),
   R = U*N*(N - 1)*abs(A.range).
rounding(_, M, U, R) => R = U*abs(M.range).

% The unit roundoff of a float array, bound when its format is.
% Only its upper bound matters.
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

reduce_size(A, M, N) :-
   view:shape_size(A.shape(), Size),
   view:shape_size(M.shape(), ReducedSize),
   N is Size // ReducedSize.

% The guaranteed error of an array.
sup_precision(A, S) :-
   get_dict(precision, A, P),
   sup(P, S).

sup(P, S), number(P) => S = P.
sup(P, S) => domain(P, D), arg(2, D, S).

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

:- end_tests(precision).
