:- module(bench_sort, [go_sort/1]).
:- use_module(library(array)).
:- use_module('../examples/sort').
:- use_module(bench, [bench_data/6]).
:- use_module(library(clpBNR)).

% The sorts of sort.pl against bench_sort.py: the same sizes, N float keys with an
% int payload, the keys distinct and scrambled, the best of 5 runs. A network does the same
% work whatever the order of the keys, so the runs after the first, on the keys the first
% sorted in place, cost the same; the radix sort takes the float keys through float_keys/3
% and its runs after the first sort keys already in order, which costs it the same passes
% too. The program is built for N at least the smallest size: a
% decision on parallelism takes the least an extent can be, and the passes are worth a
% launch each, a host loop, only when N is known to be large; left free, N could be 1 and
% the loop would be one work-group's sweep.

sizes([65536, 1048576, 4194304]).

go_sort(Device) :-
   sizes(Sizes), Sizes = [Least | _],
   forall(member(N, Sizes),
          ( bitonic(Keys, Vals, Ks, Ss, Ne), {Ne >= Least},
            numlist(1, N, Is), maplist([I, K]>>(K is ((I * 7919) mod N) + 0.5), Is, KeyList),
            N1 is N - 1, numlist(0, N1, Vs), pass_table(N, KL, SL),
            format(atom(Lb), "bitonic ~d", [N]),
            bench_data(Lb, Keys, [Keys-KeyList, Vals-Vs, Ks-KL, Ss-SL], Device, [], 5) )),
   forall(member(N, Sizes),
          ( float_keys(F, K, Ne), radix(K, Vals, Sh, Xm, Ne), {Ne >= Least},
            numlist(1, N, Is), maplist([I, X]>>(X is ((I * 7919) mod N) + 0.5), Is, KeyList),
            N1 is N - 1, numlist(0, N1, Vs), radix_table(SL, XL),
            format(atom(Lb), "radix ~d", [N]),
            bench_data(Lb, Vals, [F-KeyList, Vals-Vs, Sh-SL, Xm-XL], Device, [], 5) )).
