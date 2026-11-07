:- module(sort_tests, []).

:- use_module(library(array)).
:- use_module('../examples/sort').
:- use_module(library(array/opencl), [opencl_device/2]).

% keys(+N, -Keys): N distinct keys in a scrambled order.
keys(N, Keys) :-
   numlist(1, N, Is),
   maplist([I, K]>>(K is ((I * 7919) mod N) + 0.5), Is, Keys).

% expected(+Keys, -Sorted, -Order): the keys ascending and the positions they came from.
expected(Keys, Sorted, Order) :-
   length(Keys, N), N1 is N - 1, numlist(0, N1, Is),
   pairs_keys_values(Pairs, Keys, Is),
   msort(Pairs, SortedPairs),
   pairs_keys_values(SortedPairs, Sorted, Order).

near(Xs, Ys) :-
   maplist([X, Y]>>( X =:= Y -> true ; abs(X - Y) < 1.0e-6 * (1 + abs(X)) ), Xs, Ys).

% int_keys(+N, -Keys): N distinct ints in a scrambled order, half of them negative.
int_keys(N, Keys) :-
   numlist(1, N, Is),
   maplist([I, K]>>(K is ((I * 7919) mod N) * 3 - N), Is, Keys).

% radix_data(+Keys, +Vals, +Sh, +Xm, +KeyList, -Data): the input lists of one radix sort.
radix_data(Keys, Vals, Sh, Xm, KeyList, [Keys-KeyList, Vals-Is, Sh-SL, Xm-XL]) :-
   length(KeyList, N), N1 is N - 1, numlist(0, N1, Is),
   radix_table(SL, XL).

% data(+Keys, +Vals, +Ks, +Ss, +KeyList, -Data): the input lists of one sort of KeyList.
data(Keys, Vals, Ks, Ss, KeyList, [Keys-KeyList, Vals-Is, Ks-KL, Ss-SL]) :-
   length(KeyList, N), N1 is N - 1, numlist(0, N1, Is),
   pass_table(N, KL, SL).

:- begin_tests(sorting).

test(pass_table_of_eight, [timeout(10), true(Ks-Ss == [2, 4, 4, 8, 8, 8]-[1, 2, 1, 4, 2, 1])]) :-
   pass_table(8, Ks, Ss).

test(pass_table_is_padded_even, [timeout(10), true(L == 4)]) :-
   pass_table(4, Ks, _), length(Ks, L).

test(eval_sorts_keys_and_payload, [timeout(60)]) :-
   bitonic(Keys, Vals, Ks, Ss, _),
   keys(64, KeyList), data(Keys, Vals, Ks, Ss, KeyList, Data),
   expected(KeyList, Sorted, Order),
   eval(Keys, Data, K), eval(Vals, Data, V),
   near(Sorted, K), V == Order.

% One program for every size: N is bound by the keys given.
test(one_program_sorts_two_sizes, [timeout(300), forall(opencl_device(D, _))]) :-
   bitonic(Keys, Vals, Ks, Ss, N),
   forall(member(N0, [64, 1024]),
          ( keys(N0, KeyList), data(Keys, Vals, Ks, Ss, KeyList, Data),
            expected(KeyList, Sorted, Order),
            run(Keys, Data, K, [device(D)]), near(Sorted, K),
            run(Vals, Data, V, [device(D)]), V == Order )),
   var(N).

% The gated pairs, infinite keys, sort last, in their original order.
test(infinite_keys_sort_last, [timeout(60)]) :-
   bitonic(Keys, Vals, Ks, Ss, _),
   Inf is inf, KeyList = [3.5, Inf, 1.5, Inf, 2.5, Inf, 0.5, Inf],
   data(Keys, Vals, Ks, Ss, KeyList, Data),
   eval(Keys, Data, K), eval(Vals, Data, V),
   K = [0.5, 1.5, 2.5, 3.5, I1, I2, I3, I4], maplist(=:=(Inf), [I1, I2, I3, I4]),
   V = [6, 2, 4, 0 | Rest], msort(Rest, [1, 3, 5, 7]).

test(radix_table_has_eight_even_passes, [timeout(10), true(Sh-Xm == [0, 4, 8, 12, 16, 20, 24, 28]-[0, 0, 0, 0, 0, 0, 0, 8])]) :-
   radix_table(Sh, Xm).

% The radix sort on ints, negatives among them, against msort.
test(radix_eval_sorts_ints, [timeout(300)]) :-
   radix(Keys, Vals, Sh, Xm, _),
   int_keys(8192, KeyList), radix_data(Keys, Vals, Sh, Xm, KeyList, Data),
   expected(KeyList, Sorted, Order),
   eval(Keys, Data, K), eval(Vals, Data, V),
   K == Sorted, V == Order.

test(radix_one_program_sorts_two_sizes, [timeout(600), forall(opencl_device(D, _))]) :-
   radix(Keys, Vals, Sh, Xm, N),
   forall(member(N0, [8192, 65536]),
          ( int_keys(N0, KeyList), radix_data(Keys, Vals, Sh, Xm, KeyList, Data),
            expected(KeyList, Sorted, Order),
            run(Keys, Data, K, [device(D)]), K == Sorted,
            run(Vals, Data, V, [device(D)]), V == Order )),
   var(N).

% Float keys through their bits: negatives first, by value, inf last.
test(float_keys_order, [timeout(300), forall(opencl_device(D, _))]) :-
   float_keys(F, K, _), radix(K, Vals, Sh, Xm, _),
   Inf is inf,
   numlist(1, 8192, Is), maplist([I, X]>>( I =:= 1 -> X = Inf ; X is (((I * 7919) mod 8192) - 4096) / 7 ), Is, FL),
   length(FL, N), N1 is N - 1, numlist(0, N1, Vs), radix_table(SL, XL),
   Data = [F-FL, Vals-Vs, Sh-SL, Xm-XL],
   expected(FL, _, Order),
   run(Vals, Data, V, [device(D)]), V == Order.

:- end_tests(sorting).
