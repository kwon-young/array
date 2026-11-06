:- module(sort2, [bitonic/5, pass_table/3, radix/5, radix_table/2, float_keys/3]).
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

A radix sort, LSD, on 4-bit digits of int keys: eight passes, each a counting sort by one
digit that keeps the order of the previous. A pass takes the digit of every key, with the top
digit's sign bit flipped so that negative keys come first; counts the digits per block of 64
keys; sums the counts per digit over the blocks, and the digits below each, the offset of a
digit; sums the blocks before each within its super-block of 128 and the super-blocks before
each, the offset of a block within its digit; ranks every key among the keys of its digit
before it in its block; and scatters each key to the sum of the three, a permutation, which
the compiler takes as such and keeps the scatter parallel. The digits, counts and ranks of a
block are one work-group's, the block's slices in local memory, a sweep of one step. The passes are a host loop over a
table of shifts and top-digit masks, radix_table/2, two passes a step as the bitonic sort, so
one program serves every N, a multiple of 8192.

    radix(+Keys, +Vals, +Sh, +Xm, +N)
        Keys[N] ints and Vals[N] ints, sorted in place by ascending key; Sh[NP] and Xm[NP] the
        table; N a multiple of 8192, the names' extents. A caller sorting many keys posts
        {N >= 4096} or so, as for bitonic/5.
    radix_table(-Sh, -Xm)
        the shifts 0, 4, ..., 28 and the masks 0, ..., 0, 8 of the eight passes.
    float_keys(+F, +K, +N)
        K[N] int keys in the order of the floats F[N]: the bits of a float, its magnitude
        negated when it is negative, and inf past every finite key.
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

radix(Keys, Vals, Sh, Xm, N) :-
   Bk = 64, S = 128, Bins = 16,
   shape(Keys, [N]), shape(Vals, [N]), kind(Keys, int), kind(Vals, int),
   shape(Sh, [NP]), shape(Xm, [NP]), kind(Sh, int), kind(Xm, int), elements(Sh, 0-28), elements(Xm, 0-8),
   NB::integer(1, inf), NS::integer(1, inf), {N == NB*Bk, NB == NS*S},
   Half::integer(0, inf), {NP == 2*Half},
   shape(K1, [N]), shape(V1, [N]), kind(K1, int), kind(V1, int),
   pass_boxes(Keys, Vals, K1, V1, Sh[2*P2], Xm[2*P2], N, NB, NS, Bk, S, Bins, BoxesA),
   pass_boxes(K1, V1, Keys, Vals, Sh[2*P2 + 1], Xm[2*P2 + 1], N, NB, NS, Bk, S, Bins, BoxesB),
   append(BoxesA, BoxesB, Inner),
   over([P2:Half], Inner).

% pass_boxes(+KIn, +VIn, +KOut, +VOut, +ShE, +XmE, +N, +NB, +NS, +Bk, +S, +Bins, -Boxes): the
% boxes of one pass from KIn, VIn to KOut, VOut, by the digit at the shift ShE under the mask
% XmE: the digits Dg[NB, Bk], the counts H[NB, Bins], their sums C[Bins] and offsets Off[Bins],
% the sums G[Bins, NS] of the super-blocks, the offsets PS[Bins, NS] of a super-block and
% PB[Bins, NB] of a block, the ranks Rank[NB, Bk], and the destinations Dest[N].
pass_boxes(KIn, VIn, KOut, VOut, ShE, XmE, N, NB, NS, Bk, S, Bins, Boxes) :-
   shape(Dg, [NB, Bk]), kind(Dg, int), elements(Dg, 0-15),
   shape(H, [NB, Bins]), shape(C, [Bins]), shape(Off, [Bins]),
   shape(G, [Bins, NS]), shape(PS, [Bins, NS]), shape(PB, [Bins, NB]),
   shape(Rank, [NB, Bk]),
   shape(Dest, [N]), kind(Dest, int), elements(Dest, 0-(N-1)), permutation(Dest),
   BS is Bk*S,
   Boxes = [
      % a work-group per block, its digits, counts and ranks in local memory
      over([Bl:NB], [over([E:Bk], [Dg[Bl, E] := ((KIn[Bl*Bk + E] >> ShE) /\ 15) xor XmE]),
                     over([D:Bins], [H[Bl, D] := 0,
                                     over([E:Bk], [H[Bl, D] := H[Bl, D] + where(Dg[Bl, E] =:= D, 1, 0)])]),
                     over([E:Bk], [Rank[Bl, E] := 0,
                                   over([E2:Bk], [Rank[Bl, E] := Rank[Bl, E]
                                                     + where(E2 < E, where(Dg[Bl, E2] =:= Dg[Bl, E], 1, 0), 0)])])]),
      over([D:Bins], [C[D] := 0]),
      over([D:Bins, Bl:NB], [C[D] := C[D] + H[Bl, D]]),
      over([D:Bins], [Off[D] := 0]),
      over([D:Bins, D2:Bins], [Off[D] := Off[D] + where(D2 < D, C[D2], 0)]),
      over([D:Bins, Su:NS], [G[D, Su] := 0]),
      over([D:Bins, Su:NS, B2:S], [G[D, Su] := G[D, Su] + H[Su*S + B2, D]]),
      over([D:Bins, Su:NS], [PS[D, Su] := 0]),
      over([D:Bins, Su:NS, Su2:NS], [PS[D, Su] := PS[D, Su] + where(Su2 < Su, G[D, Su2], 0)]),
      over([D:Bins, Su:NS, B1:S], [PB[D, Su*S + B1] := 0]),
      over([D:Bins, Su:NS, B1:S, B2:S], [PB[D, Su*S + B1] := PB[D, Su*S + B1] + where(B2 < B1, H[Su*S + B2, D], 0)]),
      over([I:N], [Dest[I] := Off[Dg[I // Bk, I mod Bk]] + PS[Dg[I // Bk, I mod Bk], I // BS]
                              + PB[Dg[I // Bk, I mod Bk], I // Bk] + Rank[I // Bk, I mod Bk]]),
      over([I:N], [KOut[Dest[I]] := KIn[I], VOut[Dest[I]] := VIn[I]])
   ].

radix_table(Sh, Xm) :-
   Sh = [0, 4, 8, 12, 16, 20, 24, 28],
   Xm = [0, 0, 0, 0, 0, 0, 0, 8].

float_keys(F, K, N) :-
   shape(F, [N]), kind(F, float), shape(K, [N]), kind(K, int),
   over([I:N], [K[I] := where(bits(F[I]) < 0, -(bits(F[I]) /\ 2147483647), bits(F[I]))]).

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
