:- module(core_array, [over/3, shape/2, transpose/2, reshape/3, pad/3, shrink/3, slice/3, matmul/3, take/3,
                       fold/2, lower/3, batch/3, eval/3, info/4, choose/3, op(20, yf, [])]).
% An array is a function from an index box to values; its core terms are:
%   A ::= input(Name, Shape, Kind, Lo-Hi) | array([D:N, ...], E) | rec(S, [T:N, D:N, ...], E), E reading S before T
%   E ::= D | Number | A[E, ...] | agg(Acc, D:N, E) | where(E, E, E) | cast(F, E) | Primitive(E, ...)
% An input declares the kind (bool, int or float) and the range of its elements. Ops are exact on the
% reals but two: cast(F, E) rounds E to the format F, and agg sums in the format Acc, exactly if Acc is +.
% A dim D is a plain variable bound by array, rec or agg: never unified, only substituted. A[Es] is [](Es, A).
:- use_module(library(clpBNR)).   % the only solver: sizes, dims, kinds and bounds are its numbers

shape(input(_, Sh, _, _), Shape) => Shape = Sh.
shape(A, Shape), (A = array(Bs, _) ; A = rec(_, Bs, _)) => maplist(arg(2), Bs, Shape).

% subst(+Pairs, +T0, -T): T0 with the dims of Pairs replaced, its agg dims renamed (hygiene).
subst(S, V, T), var(V), member(K-X, S), K == V => T = X.
subst(S, agg(Op, K:N, E0), T) => T = agg(Op, F:N, E), subst([K-F | S], E0, E).
subst(S, T0, T), compound(T0) => T0 =.. [F | As0], maplist(subst(S), As0, As), T =.. [F | As].
subst(_, T0, T) => T = T0.

% over(+Dims, +E, -A): the surface array/2, renaming Dims. Where a dim is an index, a dim given
% as D:N stays in bounds, and a dim given as D takes the size of what it indexes, the same in all.
over(Ds, E0, array(Bs, E)) :- maplist(binder, Ds, S, Bs, Ms), subst(S, E0, E), sizes(Ms, E).
binder(D:N, S, B, M) => S = D-F, B = F:N, M = F:N-given.
binder(D, S, B, M) => S = D-F, B = F:N, M = F:N-inferred.
sizes(Ms, [](Is, A)), nonvar(A) => shape(A, Sh), maplist(size(Ms), Is, Sh), maplist(sizes(Ms), Is).
sizes(Ms, agg(_, B, E)) => sizes([B-given | Ms], E).
sizes(Ms, E), compound(E) => E =.. [_ | As], maplist(sizes(Ms), As).
sizes(_, _) => true.
size(Ms, I, Dim), var(I), member(F:N-given, Ms), F == I => {N =< Dim}.
size(Ms, I, Dim), var(I), member(F:N-inferred, Ms), F == I => N = Dim.
size(_, _, _) => true.

transpose(A, T) :- over([I, J], A[J, I], T).
shrink(A, S-E, R) :- shape(A, [_ | Sh]), eq(M, E-S), same_length(Sh, Is), over([I:M | Is], []([I+S | Is], A), R).
slice(A, B:E:K, R) :- shape(A, [_ | Sh]), divmod(E-B+K-1, K, M, _), same_length(Sh, Is),   % numpy's A[B:E:K]
   over([I:M | Is], []([B + K*I | Is], A), R).
pad(A, L-H, R) :- shape(A, [N | Sh]), eq(M, N+L+H), same_length(Sh, Is),
   over([I:M | Is], where(L =< I, where(I < L+N, []([I-L | Is], A), 0), 0), R).
reshape(A, Sh, R) :- shape(A, Sh0), prod(Sh0, P), prod(Sh, P), same_length(Sh, Is),
   maplist([I, N, I:N]>>true, Is, Sh, Ds), lin(Sh, Is, L), unlin(Sh0, L, Js), over(Ds, [](Js, A), R).
matmul(A, B, C) :- shape(A, [_, K]), shape(B, [K, _]), over([I, J], agg(+, L:K, A[I, L] * B[L, J]), C).
take(A, Idx, R) :- over([I], A[Idx[I]], R).   % a gather: an index is an expression
fold(R, A) :- shape(R, [N | Sh]), same_length(Sh, Is), over(Is, []([N-1 | Is], R), A).   % last state
eq(X, E) :- X::integer, {X == E}.   prod(Sh, P) :- Sh::integer, foldl([N, P0, P1]>>eq(P1, P0*N), Sh, 1, P).
lin([_ | Sh], [I | Is], L) :- foldl([N, J, L0, L0*N+J]>>true, Sh, Is, I, L).
unlin(Sh, L, Js) :- reverse(Sh, Rs), foldl([N, L0 mod N, L0, L0//N]>>true, Rs, RJs, L, _), reverse(RJs, Js).
divmod(A, B, Q, R) :- [Q, R]::integer, {A == B*Q + R, 0 =< R, R =< B-1}.   % clpBNR has no // nor mod

% Lowering. beta(+Under, +E0, -E): E0 with each read of an array its body at the read index (fusion), but
% a read under an agg of an array that sums, kept for a buffer of its own; Under is agg or no.
beta(U, [](Is, A), T), nonvar(A), A = array(_, E), (U == no ; \+ sums(E)) => apply(A, Is, E1), beta(U, E1, T).
beta(U, [](Is0, A), T), nonvar(A), A = array(_, _) => maplist(beta(U), Is0, Is), T = [](Is, A).
beta(_, agg(Op, B, E0), T) => T = agg(Op, B, E), beta(agg, E0, E).
beta(U, E0, T), compound(E0) => E0 =.. [F | As0], maplist(beta(U), As0, As), T =.. [F | As].
beta(_, E, T) => T = E.
apply(array(Bs, E), Is, T) :- maplist(arg(1), Bs, Ds), pairs_keys_values(S, Ds, Is), subst(S, E, T).
sums(E) :- sub_term(T, E), compound(T), T = agg(_, _, _), !.
% loads(+Bufs, +E0, -E): E0 with each read of an input, or of a buffer in Bufs, a load.
loads(M, [](Is0, A), T) => maplist(loads(M), Is0, Is), buffer(M, A, Name, Sh), lin(Sh, Is, L), T = load(Name, L).
loads(M, E0, T), compound(E0) => E0 =.. [F | As0], maplist(loads(M), As0, As), T =.. [F | As].
loads(_, E, T) => T = E.
buffer(_, input(Name, Sh, _, _), N, S) => N = Name, S = Sh.
buffer(M, A, N, Sh), member(A1-(N1-Sh1), M), A1 =@= A => N = N1, Sh = Sh1.   % an array, a rec or its states

% lower(+Out, +A, -Kernels): the kernels storing A into Out, after those of the buffers b0, b1, ... it reads.
lower(Out, A, Ks) :- lower(Out, A, []-[], _-Rs), reverse(Rs, Ks).
lower(Out, array(Bs, E), Tb0, Tb) => beta(no, E, E1), deps(E1, Tb0, M-Ks), loads(M, E1, E2),
   store(Out, Bs, E2, St), nest(Bs, par, St, K), shape(array(Bs, E), Sh), Tb = M-[kernel(Out, Sh, K) | Ks].
lower(Out, R, Tb0, Tb), R = rec(S, [T:N | Bs], E) => shape(R, Sh), beta(no, E, E1), deps(E1, Tb0, M-Ks),
   loads([S-(Out-Sh) | M], E1, E2), store(Out, [T:N | Bs], E2, St), batch(R, Batch, Others),
   nest(Others, par, St, K0), nest(Batch, par, for(seq, T, N, K0), K), Tb = M-[kernel(Out, Sh, K) | Ks].
% deps(+E, +Tb0, -Tb): Tb0, Buffer-(Name-Shape) pairs and kernels, with the buffers E reads, each lowered once.
deps(E, Tb0, Tb) :- bufs(E, [], Rs), foldl(dep, Rs, Tb0, Tb).
dep(R, M-Ks, Tb), member(R1-_, M), R1 =@= R => Tb = M-Ks.
dep(R, M-Ks, Tb) => length(M, I), atom_concat(b, I, B), shape(R, Sh), lower(B, R, [R-(B-Sh) | M]-Ks, Tb).
bufs(T, Rs0, Rs), compound(T), (T = rec(_, _, _) ; T = array(_, _)) => Rs = [T | Rs0].
bufs(T, Rs0, Rs), compound(T) => T =.. [_ | As], foldl(bufs, As, Rs0, Rs).
bufs(_, Rs0, Rs) => Rs = Rs0.
store(Out, Bs, E, store(Out, L, E)) :- maplist(arg(1), Bs, Ds), maplist(arg(2), Bs, Sh), lin(Sh, Ds, L).
nest(Bs, Kind, Body, K) :- reverse(Bs, Rs), foldl([D:N, B0, for(Kind, D, N, B0)]>>true, Rs, Body, K).
% batch(+Rec, -Batch, -Others): a batch dim, run in parallel around the steps, is kept by every read of the states.
batch(rec(S, [_ | Bs], E), Batch, Others) :- partition(kept(S, E, Bs), Bs, Batch, Others).
kept(S, E, Bs, D:_) :- once((nth1(P, Bs, D1:_), D1 == D)),
   forall((sub_term(R, E), compound(R), R = []([_ | Is], S1), S1 == S), (nth1(P, Is, I), I == D)).

% eval(+A, +Inputs, -Vals): runs the kernels of A on Inputs, Name-List pairs, row-major, exactly.
eval(A, Inputs, Vals) :- lower(out, A, Ks), maplist([N-L, N-T]>>(T =.. [d | L]), Inputs, Env0),
   foldl(run, Ks, Env0, Env), memberchk(out-Out, Env), Out =.. [_ | Vals].
run(kernel(Name, Sh, K), Env, [Name-B | Env]) :- prod(Sh, Size), functor(B, d, Size), exec(K, [Name-B | Env]).
exec(for(_, D, N, B), Env) => N1 is N-1, forall(between(0, N1, D), exec(B, Env)).
exec(store(Buf, L, E), Env) => memberchk(Buf-T, Env), ev(Env, L, I), ev(Env, E, V), I1 is I+1, nb_setarg(I1, T, V).
ev(Env, load(B, L), V) => memberchk(B-T, Env), ev(Env, L, I), I1 is I+1, arg(I1, T, V).
ev(Env, where(C, A, B), V) => ev(Env, C, X), nth0(X, [B, A], E), ev(Env, E, V).
ev(Env, agg(_, K:N, E), V) => N1 is N-1, aggregate_all(sum(X), (between(0, N1, K), ev(Env, E, X)), V).
ev(Env, cast(_, E), V) => ev(Env, E, V).
ev(Env, E, V), E =.. [Op | As], cmp(Op, _) => maplist(ev(Env), As, Xs), G =.. [Op | Xs], aggregate_all(count, G, V).
ev(Env, E, V) => E =.. [Op | As], maplist(ev(Env), As, Xs), E1 =.. [Op | Xs], V is E1.
cmp(<, <). cmp(=<, =<). cmp(=:=, ==).

% Analysis of a generic element. info(?A, ?Kind, -Lo-Hi, -Err): the kind of the elements of A, an enclosure of
% their exact values and a bound on the error of their computed ones, once each read is proved in its box.
info(A, Kind, Lo-Hi, Err) :- shape(A, Sh), maplist(index, Sh, Is), an([], [](Is, A), v(X, K, Err)),
   kind(Kind, K), range(X, [Lo, Hi]).
kind(Kind, K) :- K::integer(0, 2), when((nonvar(Kind) ; ground(K)), once(nth0(K, [bool, int, float], Kind))).
index(N, I) :- I::integer(0, inf), {I =< N-1}.   kmax(A, B, K) :- K::integer(0, 2), {K == max(A, B)}.
% an(+Path, +E, -v(X, K, R)): E is X exactly, of kind K, and is computed within R, where Path holds.
an(_, E, V), var(E) => V = v(E, 1, 0).   % a dim is an int
an(_, E, V), (E == 0 ; E == 1) => V = v(E, 0, 0).
an(_, E, V), integer(E) => V = v(E, 1, 0).
an(_, E, V), float(E) => V = v(E, 2, 0).
an(P, [](Is, A), V) => maplist(exact(P), Is, Xs), shape(A, Sh), in_bounds(P, Xs, Sh, [](Is, A)), facts(P, Is, A, V).
an(P, where(C, A, B), V) => an(P, C, v(F, _, RF)), an([F-1 | P], A, v(XA, KA, RA)), an([F-0 | P], B, v(XB, KB, RB)),
   {X is F*XA + (1-F)*XB}, kmax(KA, KB, K), sup(max(RA, RB) + RF*abs(XA-XB), R), V = v(X, K, R).
an(P, agg(F, D:N, E), V) => index(N, D), an(P, E, v(Y, KY, RY)), {X is N*Y}, kmax(1, KY, K),
   acc(F, N, Y, KY, RY, R), V = v(X, K, R).
an(P, cast(F, E), V) => an(P, E, v(X, K, Q)), sup(abs(X) + Q, M), rnd(F, K, M, Q, Q1), sup(Q + Q1, R), V = v(X, K, R).
an(P, A // B, V) => maplist(exact(P), [A, B], [XA, XB]), divmod(XA, XB, X, _), V = v(X, 1, 0).
an(P, A mod B, V) => maplist(exact(P), [A, B], [XA, XB]), divmod(XA, XB, _, X), V = v(X, 1, 0).
an(P, E, V), E =.. [Op, A, B], cmp(Op, C) => maplist(an(P), [A, B], [v(XA, _, RA), v(XB, _, RB)]),
   G =.. [C, XA, XB], X::boolean, {X == G}, R is sign(RA + RB), V = v(X, 0, R).   % R = 1: it may flip
an(P, E, V) => E =.. [Op | As], maplist(an(P), As, Vs), maplist(v, Vs, Xs, Ks, Rs), E1 =.. [Op | Xs],
   {X is E1}, op_kind(Op, Ks, K), mvt(Op, Xs, Rs, R), V = v(X, K, R).
v(v(X, K, R), X, K, R).   exact(P, E, X) :- an(P, E, v(X, _, 0)).   % an index is exact
facts(_, _, input(_, _, Kind, Lo-Hi), V) => kind(Kind, K), X::real(Lo, Hi), V = v(X, K, 0).
facts(P, Is, A, V), A = array(_, E0), \+ sums(E0) => apply(A, Is, E), an(P, E, V).   % inlined: precise
facts(_, _, A, V), A = array(_, _) => copy_term(A, A1, _), summary(A1, KD, XD, R), K::KD, X::XD, V = v(X, K, R).
facts(_, _, rec(_, _, E), V) => \+ rounds(E), X::real, K::integer(0, 2), V = v(X, K, 0).   % no fixpoint: unknown
rounds(E) :- sub_term(T, E), compound(T), (T = cast(_, _) ; T = agg(F, _, _), F \== +), !.
:- table summary/4.   % summary(+A, -KD, -XD, -R): an array that sums, analysed once for all its elements
summary(A, integer(KL, KH), real(Lo, Hi), R) :- shape(A, Sh), maplist(index, Sh, Is), apply(A, Is, E),
   an([], E, v(X, K, R)), range(X, [Lo, Hi]), range(K, [KL, KH]).
op_kind(Op, _, K), memberchk(Op, [sin, cos, exp, log, sqrt]) => K = 2.
op_kind(_, Ks, K) => foldl(kmax, Ks, 1, K).   % arithmetic on bools is on ints
in_bounds(P, Xs, Sh, _), forall(maplist([F-B]>>(F = B), P), maplist(below, Xs, Sh)) => true.
in_bounds(_, _, _, Read) => domain_error(in_bounds, Read).
below(X, N) :- range(X, [Lo, Hi]), Lo >= 0, Hi =< N-1.
% mvt(+Op, +Xs, +Rs, -R): the mean value theorem: the derivatives over the Xs widened by Rs, times the Rs.
mvt(_, _, Rs, R), maplist(==(0), Rs) => R = 0.
mvt(Op, Xs, Rs, R) => maplist(widen, Xs, Rs, Ws), E =.. [Op | Ws], d(E, Ds),
   foldl([D, Q, S0, S0 + abs(D)*Q]>>true, Ds, Rs, 0, S), sup(S, R).
widen(X, R, W) :- D::real(-R, R), {W is X + D}.
sup(E, U) :- {X is E}, range(X, [_, U]).   % the bounds of clpBNR are rounded outward: U is sound
d(_+_, [1, 1]). d(_-_, [1, -1]). d(-_, [-1]). d(A*B, [B, A]). d(A/B, [1/B, A/(B*B)]). d(abs(_), [1]).
d(exp(A), [exp(A)]). d(log(A), [1/A]). d(sqrt(A), [1/(2*sqrt(A))]). d(max(_, _), [1, 1]). d(min(_, _), [1, 1]).

% Formats, cheapest first: fixed(IntBits, FracBits) is signed, float(ExpBits, MantBits) counts the hidden bit.
fmt(int8, fixed(7, 0)). fmt(int16, fixed(15, 0)). fmt(bf16, float(8, 8)). fmt(fp16, float(5, 11)).
fmt(int32, fixed(31, 0)). fmt(fp32, float(8, 24)).
% unit(+F, -Max, -Ex, -A, -U): F holds |x| =< Max, the ints up to Ex exactly, and rounds x by A + U*|x|.
unit(F, Max, Ex, A, U), fmt(F, fixed(I, Fr)) => Max is 2.0**I - 2.0**(-Fr), Ex = Max, A is 2.0**(-Fr-1), U = 0.
unit(F, Max, Ex, A, U), fmt(F, float(E, P)) => B is 2**(E-1) - 1, Max is (2 - 2.0**(1-P)) * 2.0**B,
   Ex is 2.0**P, A is 2.0**(1-B-P), U is 2.0**(-P).   % A: the subnormals
% rnd(+F, +K, +M, +R0, -R): the error of rounding to F a value of magnitude at most M, kind K and error R0.
rnd(F, K, M, R0, R), unit(F, _, Ex, _, _), sup(K, Kh), Kh < 2, R0 =:= 0, M =< Ex => R = 0.   % Ex =< Max
rnd(F, _, M, _, R), unit(F, Max, _, A, U) => M =< Max, sup(A + U*M, R).   % fails on an overflow
% acc(+F, +N, +Y, +K, +RY, -R): the error of a sum of N terms Y of error RY, each partial sum rounded to F.
acc(+, N, _, _, RY, R) => sup(N*RY, R).
acc(F, N, Y, K, RY, R) => sup(N*(abs(Y) + RY), S), rnd(F, K, S, RY, R1), unit(F, Max, _, _, U), (N-1)*U < 1,
   sup(N*RY + (N-1)*R1 / (1 - (N-1)*U), R), S + R =< Max.
choose(Fs, A, Eps) :- maplist(fmt, Fs, _), info(A, _, _, E), E =< Eps, !.   % the first Fs, in menu order, within Eps
