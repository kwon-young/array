:- module(sort2, [bitonic/5, pass_table/3]).
:- use_module(core2).
:- use_module(library(clpBNR)).

/** <module> A bitonic sort as boxes

A sorting network: a fixed sequence of compare-exchanges that depends on the size alone,
never on the data, so every pass is one parallel box. For N = 2^n keys there are n(n+1)/2
passes; pass p has a block size k and a stride j, element i's partner is i xor j, the block
i /\ k = 0 sorts ascending, the other descending, and the lower of a pair, i /\ j = 0, keeps
the lesser key under ascending, the greater under descending. A payload follows its key.

The passes are a host loop over a table of (k, j) pairs the host computes, pass_table/3, so
that one program serves every N: the keys read the partner's key through xor, which the
bounds rule admits with N declared a power of two and the strides ranging in 0..N-1. The
table is padded to an even length with a stride of 0, a pass that moves nothing, and each
step of the loop runs two passes, the keys and payloads to a second pair of arrays and back,
so no copy is needed. The loop is a host loop, a launch per pass, when N is known to be
large: a decision on parallelism takes the least an extent can be, so a caller sorting many
keys posts {N >= 4096} or so on the extent N; left free, N may be 1 and the passes become
one work-group's sweep, right for a few keys, a hundred times slower for a million.

    bitonic(+Keys, +Vals, +Ks, +Ss, +N)
        Keys[N] floats and Vals[N] ints, sorted in place by ascending key; Ks[NP] and Ss[NP]
        the table, NP even; N a power of two, the names' extents.
    pass_table(+N, -Ks, -Ss)
        the table of N, a power of two, as two lists.
*/

bitonic(Keys, Vals, Ks, Ss, N) :-
   power_of_two(N),
   shape(Keys, [N]), shape(Vals, [N]), kind(Keys, float), kind(Vals, int),
   shape(Ks, [NP]), shape(Ss, [NP]), kind(Ks, int), kind(Ss, int),
   elements(Ks, 0-N), elements(Ss, 0-(N-1)),
   Half::integer(0, inf), {NP == 2*Half},
   shape(K1, [N]), shape(V1, [N]),
   pass(Keys, Vals, Ks[2*P2], Ss[2*P2], I1, Key1, Val1),
   pass(K1, V1, Ks[2*P2 + 1], Ss[2*P2 + 1], I0, Key0, Val0),
   over([P2:Half], [over([I1:N], [K1[I1] := Key1, V1[I1] := Val1]),
                    over([I0:N], [Keys[I0] := Key0, Vals[I0] := Val0])]).

% pass(+KIn, +VIn, +K, +J, +I, -Key, -Val): the key and payload element I takes in a pass of
% block size K and stride J, from the arrays KIn and VIn.
pass(KIn, VIn, K, J, I, Key, Val) :-
   A = KIn[I], B = KIn[I xor J],
   Lower = (I /\ J =:= 0), Up = (I /\ K =:= 0),
   Key = where(Lower, where(Up, min(A, B), max(A, B)), where(Up, max(A, B), min(A, B))),
   Take = where(Lower =:= Up, B < A, A < B),
   Val = where(Take, VIn[I xor J], VIn[I]).

pass_table(N, Ks, Ss) :-
   must_be(positive_integer, N),
   N /\ (N-1) =:= 0,
   findall(K-J, ( between(1, N, K), K /\ (K-1) =:= 0, K >= 2,
                  between(1, K, J), J /\ (J-1) =:= 0, J < K ), Pairs0),
   predsort(pass_order, Pairs0, Pairs1),
   (  length(Pairs1, L), L mod 2 =:= 0
   -> Pairs = Pairs1
   ;  append(Pairs1, [0-0], Pairs)
   ),
   pairs_keys_values(Pairs, Ks, Ss).

% pass_order(-Order, +Pass1, +Pass2): the blocks grow, and within a block the strides shrink.
pass_order(Order, K1-J1, K2-J2) :-
   (  K1 =:= K2
   -> compare(Order, J2, J1)
   ;  compare(Order, K1, K2)
   ).
