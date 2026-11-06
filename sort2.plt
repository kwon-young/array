:- use_module(core2).
:- use_module(compile2).
:- use_module(sort2).
:- use_module(opencl, [opencl_device/2]).

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

% data(+Keys, +Vals, +Ks, +Ss, +KeyList, -Data): the input lists of one sort of KeyList.
data(Keys, Vals, Ks, Ss, KeyList, [Keys-KeyList, Vals-Is, Ks-KL, Ss-SL]) :-
   length(KeyList, N), N1 is N - 1, numlist(0, N1, Is),
   pass_table(N, KL, SL).

:- begin_tests(sort2).

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

:- end_tests(sort2).
