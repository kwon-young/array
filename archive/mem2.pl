:- use_module(library(clpfd)).
:- use_module(library(csv)).

rows(Rows2) :-
   % csv_read_file("/home/kwon-young/prog/minimalloc/benchmarks/challenging/K.1048576.csv", [_Header | Rows]),
   csv_read_file("/home/kwon-young/prog/minimalloc/benchmarks/challenging/A.1048576.csv", [_Header | Rows]),
   % csv_read_file("/home/kwon-young/prog/minimalloc/benchmarks/challenging/A.1048576.out.csv", [_Header | Rows]),
   % csv_read_file("/home/kwon-young/prog/minimalloc/benchmarks/examples/input.12.out.csv", [_Header | Rows]),
   % csv_read_file("/home/kwon-young/prog/minimalloc/benchmarks/examples/input.12.csv", [_Header | Rows]),
   % length(First, 60),
   % append(First, _, Rows),
   list_to_ord_set(Rows, Set),
   maplist(row_row, Set, Rows2),
   % reverse(Lists, RLists),
   % transpose(Lists, T).
   true.

% row_row(row(Id, Lower, Upper, Size, Offset), row(Id, Lower, Upper, Size, Offset, _Height)).
row_row(row(Id, Lower, Upper, Size), row(Id, Lower, Upper, Size, _Offset, _Height)).

row_list(Row, List) :-
   Row =.. [_ | List].

% intersect(L1, R1, [L2, R2, _, _]) :-
%    intersect(L1, R1, L2, R2).
% intersect(L1, R1, L2, R2) :-
%    R1 #> L2 #/\ R2 #> L1.
intersect(L1, R1, row(_, L2, R2, _, _, _)) :-
   R1 > L2, R2 > L1.

% :- table intersect/2.

intersect(row(_, L1, R1, _, _, _), row(_, L2, R2, _, _, _)) :-
   R1 > L2, R2 > L1.

add(A, B, C) :-
   C #= A + B.

max([], _, Max, Max).
max([Row | Rows], N, A, Max) :-
   arg(N, Row, B),
   C is max(A, B),
   max(Rows, N, C, Max).

% max([], _Op, _Res).
% max([H | T], Op, Res) :-
%    foldl([A, B, max(A, B)]>>true, T, H, Max),
%    call(Op, Max, Res).
% min([], _Op, _Res).
% min([H | T], Op, Res) :-
%    foldl([A, B, min(A, B)]>>true, T, H, Min),
%    call(Op, Min, Res).

lower_bound([]).
lower_bound([B | Bs]) :-
   lower_bound(B, Bs),
   lower_bound(Bs).
lower_bound([L1, R1, Oi, _], Bs) :-
   include(intersect(L1, R1), Bs, InterBs),
   maplist(last, InterBs, Hjs),
   max(Hjs, #=, Oi).

index_monotonic([]).
index_monotonic([B | Bs]) :-
   maplist(index_monotonic(B), Bs),
   index_monotonic(Bs).

index_monotonic([I, Oi], [J, Oj]) :-
   Oi #= Oj #<==> I #> J.

dominated([]).
dominated([B | Bs]) :-
   dominated(B, Bs),
   dominated(Bs).
dominated([Oi, _], Bs) :-
   maplist(nth1(2), Bs, Heights),
   min(Heights, #>, Oi).

main(C, Rects) :-
   % rows([Ids, Lower, Upper, Sizes, Offsets]),
   rows([_Ids, Lower, Upper, Sizes]),
   same_length(Ids, Lower),
   length(Ids, N),
   Ids ins 1..N,
   all_distinct(Ids),
   same_length(Ids, Width),
   maplist(add, Lower, Width, Upper),
   same_length(Ids, Offsets),
   Offsets ins 0..C,
   same_length(Ids, Heights),
   maplist(add, Offsets, Sizes, Heights),
   Heights ins 0..C,

   transpose([Lower, Upper, Offsets, Heights], LowerBounds),
   reverse(LowerBounds, RLowerBounds),
   lower_bound(RLowerBounds),
   
   chain(Offsets, #=<),

   transpose([Ids, Offsets], IndexMonotonic),
   reverse(IndexMonotonic, RIndexMonotonic),
   index_monotonic(RIndexMonotonic),

   transpose([Offsets, Heights], Dominated),
   dominated(Dominated),

   label(Ids),
   transpose([Ids, Lower, Width, Sizes, Offsets], Rows),
   maplist([Row, Rect]>>(Rect =.. [rect | Row]), Rows, Rects).

cross_sections(Lower, Upper, Rows, Xs) :-
   append(Lower, Upper, LowerUpper),
   list_to_ord_set(LowerUpper, [H | T]),
   foldl(cross_sections(Rows), T, Xs, H, _).
cross_sections(Rows, End, X, Start, End) :-
   include(intersect(Start, End), Rows, X).

same_offset(Bi, Bj) :-
   arg(5, Bi, O),
   arg(5, Bj, O).

minimalloc(C, Rows) :-
   rows(Rows),
   maplist(row_list, Rows, Lists),
   transpose(Lists, [_Id, Lower, Upper, _Sizes, _Offsets, _Heights]),
   % maplist([Row]>>when(ground(Row), format("~p~n", [Row])), Rows),
   cross_sections(Lower, Upper, Rows, Xs),
   minimalloc(Rows, C, Xs, 0, []).

assign_offset([], B, O) :-
   arg(5, B, O),
   arg(6, B, H),
   arg(4, B, Size),
   H is O + Size.
assign_offset([Bj | S], Bi, Max1) :-
   (  intersect(Bi, Bj)
   -> arg(6, Bj, Heightj),
      Max2 is max(Max1, Heightj)
   ;  Max2 = Max1
   ),
   assign_offset(S, Bi, Max2).

index_monotonic([], Bi, Imax) :-
   arg(1, Bi, I),
   I >= Imax.
index_monotonic([Bj | S], Bi, Max1) :-
   (  arg(5, Bi, O), arg(5, Bj, O)
   -> arg(1, Bj, J),
      Max2 is max(Max1, J)
   ;  Max2 = Max1
   ),
   index_monotonic(S, Bi, Max2).

dominated([], _, Bi, Hmin) :-
   arg(5, Bi, Oi),
   Oi < Hmin.
dominated([Bj | U], S, Bi, Min1) :-
   dominated_(S, Bj, 0, OjS),
   arg(4, Bj, Zj),
   HjS is OjS + Zj,
   Min2 is min(Min1, HjS),
   dominated(U, S, Bi, Min2).

dominated_([], _, Max, Max).
dominated_([Bi | S], Bj, Max1, Max) :-
   (  intersect(Bi, Bj)
   -> arg(6, Bi, Hi),
      Max2 is max(Max1, Hi)
   ;  Max2 = Max1
   ),
   dominated_(S, Bj, Max2, Max).

section_inference([], C, _, Max) :-
   Max =< C.
section_inference([X | Xs], C, S, Max1) :-
   ord_intersection(S, X, Inter, Diff),
   maplist(arg(6), Inter, Heights),
   (  Heights = [_|_]
   -> max_list(Heights, SHeight)
   ;  SHeight = 0
   ),
   maplist(arg(4), Diff, Sizes),
   sum_list(Sizes, UHeight),
   Max2 is max(Max1, SHeight + UHeight),
   section_inference(Xs, C, S, Max2).

minimalloc([], _, _, _, _).
minimalloc(U1, C, Xs, MaxOffset1, S1) :-
   U1 = [_|_],
   member(Bi, U1),
   assign_offset(S1, Bi, 0),
   % offset monotonic
   arg(5, Bi, Oi),
   Oi >= MaxOffset1,
   index_monotonic(S1, Bi, 0),
   dominated(U1, S1, Bi, C),
   section_inference(Xs, C, S1, 0),
   format("~p~n", [Bi]),
   ord_subtract(U1, [Bi], U2),
   ord_union(S1, [Bi], S2),
   MaxOffset2 is max(Oi, MaxOffset1),
   maplist([U, [Lower, Upper]]>>(arg(2, U, Lower), arg(3, U, Upper)), U2, Pairs),
   append(Pairs, Bounds),
   list_to_ord_set(Bounds, Set),
   split(Set, U2, Us),
   minimalloc_(Us, C, Xs, MaxOffset2, S2).
minimalloc_([], _, _, _, _).
minimalloc_([U | Us], C, Xs, MaxOffset, S) :-
   minimalloc(U, C, Xs, MaxOffset, S),
   minimalloc_(Us, C, Xs, MaxOffset, S).

split([], Us, [Us]).
split([Bound | Bounds], Us, [Left | Rights]) :-
   (  split(Us, Bound, Left, Right), Left \= [], Right \= []
   -> split(Bounds, Right, Rights)
   ;  split(Bounds, Us, [Left | Rights])
   ).

split([], _, [], []).
split([U | Us], Bound, Left, Right) :-
   (  arg(3, U, Upper), Upper =< Bound
   -> Left = [U | Left1],
      split(Us, Bound, Left1, Right)
   ;  arg(2, U, Lower), Bound =< Lower
   -> Right = [U | Right1],
      split(Us, Bound, Left, Right1)
   ).
:- begin_tests(mem2).

test(disjoint1, [fail]) :-
   intersect(0, 1, 1, 2).

test(disjoint1, [fail]) :-
   intersect(0, 1, 2, 3).

test(disjoint2, [fail]) :-
   intersect(1, 2, 0, 1).

test(inter1) :-
   intersect(0, 2, 1, 3).

test(inter2) :-
   intersect(1, 3, 0, 2).

test(inter3) :-
   intersect(1, 3, 0, 3).

:- end_tests(mem2).
