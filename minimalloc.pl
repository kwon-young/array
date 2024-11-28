:- use_module(library(record)).
:- use_module(library(csv)).
:- use_module(library(macros)).
:- use_module(library(rbtrees)).
:- use_module(library(clpfd)).

#define(id, 1).
#define(upper, 3).

:- record row(id, low, upper, size).
% :- record row(id, low, upper, size, offset).
:- record b(id, low, upper, size, offset, width, height, area, index, total).
:- record section(floor, total, start, end, u, s).

rows(In, Buffers) :-
   rows(In, Buffers, []).

rows(In, Buffers, Options) :-
   csv_read_file(In, [_Header | AllRows]),
   (  option(head(Head), Options)
   -> length(Rows, Head),
      append(Rows, _, AllRows)
   ;  Rows = AllRows
   ),
   maplist(row_b, Rows, Buffers).

row_b(Row, B) :-
   row_id(Row, Id),
   row_low(Row, Low),
   row_upper(Row, Upper),
   row_size(Row, Size),
   Offset = 0,
   Width is Upper - Low,
   Height is Offset + Size,
   Area is Width * Size,
   make_b([id(Id), low(Low), upper(Upper), size(Size), offset(Offset), width(Width),
           height(Height), area(Area), index(Id), total(0)], B).

inside(Point, B) :-
   b_low(B, L),
   b_upper(B, U),
   L < Point, Point < U.

buffers_cuts(Buffers, Cuts) :-
   maplist(b_low, Buffers, Low),
   % min_list(Low, MinLow),
   maplist(b_upper, Buffers, Upper),
   append(Low, Upper, LowUpper),
   % LowUpper = [MinLow | Upper],
   list_to_ord_set(LowUpper, Cuts).

overlap(L1, U1, B2) :-
   b_low(B2, L2),
   b_upper(B2, U2),
   U1 > L2, L1 < U2.

overlap(B1, B2) :-
   b_low(B1, L1),
   b_upper(B1, U1),
   b_low(B2, L2),
   b_upper(B2, U2),
   U1 > L2, L1 < U2.

sections(Buffers, [Cut | Cuts], MergedSections) :-
   % TODO: need to merge successive sections where the successor is strictly a subset of the predecessor.
   foldl(cross_section(Buffers), Cuts, Sections, Cut, _),
   % merge_sections(Sections, MergedSections).
   MergedSections = Sections.

cross_section(Bs, End, Section, Start, End) :-
   include(overlap(Start, End), Bs, Overlap),
   list_to_ord_set(Overlap, Set),
   maplist(b_size, Set, Sizes),
   sum_list(Sizes, Total),
   maplist({Total}/[B]>>(b_total(B, T1), T2 is max(Total, T1), set_total_of_b(T2, B)),
           Set),
   make_section([floor(0), total(Total), start(Start), end(End), u(Set), s([])],
                Section).

merge_sections([X1 | X1s], X2s) :-
   merge_sections(X1s, X1, X2s).

merge_sections([], X, [X]).
merge_sections([X1 | X1s], X, [X3 | X3s]) :-
   (  merge_section(X, X1, X2)
   -> merge_sections(X1s, X2, [X3 | X3s])
   ;  X3 = X,
      merge_sections(X1s, X1, X3s)
   ).

merge_section(X1, X2, X3) :-
   section_u(X1, U1),
   section_u(X2, U2),
   maplist({U2}/[B1]>>maplist(overlap(B1), U2), U1),
   ord_union(U1, U2, U),
   section_start(X1, Start),
   section_end(X2, End),
   section_floor(X1, F1),
   section_floor(X2, F2),
   Floor is max(F1, F2),
   maplist(b_size, U, Sizes),
   sum_list(Sizes, Total),
   section_s(X1, S1),
   section_s(X2, S2),
   ord_union(S1, S2, S),
   make_section([floor(Floor), total(Total), start(Start), end(End), u(U), s(S)], X3).

left(End, B) :-
   b_upper(B, Upper),
   Upper =< End.

buffers_partitions(Buffers, Partitions) :-
   buffers_cuts(Buffers, Cuts),
   sections(Buffers, Cuts, [X | Xs]),
   sections_partitions(Xs, X, [], Partitions).

add_section(X, Left, P) :-
   section_u(X, U),
   (  U = []
   -> Left = P
   ;  P = [X | Left]
   ).
add_partition([], []).
add_partition([X|Xs], [[X|Xs]]).
add_partition([], Ps, Ps).
add_partition([X|Xs], [[X|Xs] | Ps], Ps).

sections_partitions([X | Xs], Partitions) :-
   sections_partitions(Xs, X, [], Partitions).
sections_partitions([], X, Left, Ps) :-
   add_section(X, Left, P1),
   reverse(P1, P),
   add_partition(P, Ps).
sections_partitions([X1 | Xs], X, Left, Ps) :-
   section_end(X, End),
   section_u(X, U),
   add_section(X, Left, P1),
   (  maplist(left(End), U)
   -> reverse(P1, P),
      add_partition(P, Ps, Rest),
      sections_partitions(Xs, X1, [], Rest)
   ;  sections_partitions(Xs, X1, P1, Ps)
   ).

b_sort([], Order, B1, B2) :-
   (  B1 == B2
   -> Order = (=)
   ;  Order = (<)
   ).
b_sort([Key-Op | Keys], Order, B1, B2) :-
   b_data(Key, B1, V1),
   b_data(Key, B2, V2),
   (  call(Op, V1, V2)
   -> Order = <
   ;  call(Op, V2, V1)
   -> Order = >
   ;  b_sort(Keys, Order, B1, B2)
   ).

round_robin(Hs, C, Limit, Partitions) :-
   round_robin_(Hs, Hs, C, Partitions, Limit).

round_robin_([], Hs, C, Partitions, NodeLimit) :-
   NodeLimit2 is NodeLimit*2,
   round_robin_(Hs, Hs, C, Partitions, NodeLimit2).
round_robin_([Heuristic | Heuristics], Hs, C, Partitions, NodeLimit) :-
   % format("~p, ~p~n", [NodeLimit, Heuristic]),
   call_with_inference_limit(
      time(maplist(partition_inference(C, Heuristic), Partitions)),
      NodeLimit,
      Result),
   (  Result == inference_limit_exceeded
   -> round_robin_(Heuristics, Hs, C, Partitions, NodeLimit)
   ;  true
   ).

partition_inference(C, Heuristic, Partition) :-
   maplist(section_u, Partition, Us),
   append(Us, Buffers),
   predsort(b_sort(Heuristic), Buffers, Sorted),
   foldl([B, I1, I2]>>(set_index_of_b(I1, B), I2 is I1 + 1), Sorted, 0, _),
   % maplist([B]>>(b_id(B, Id), format("static ordering: ~p~n", [Id])), Sorted),
   once(inference(Sorted, Partition, C, Heuristic, 0, 0)).

min_height(Buffers, MinHeight) :-
   maplist(b_height, Buffers, Heights),
   min_list(Heights, MinHeight).

inference([], _, _, _, _).
inference(Buffers, Sections, C, Heuristic, MinOffset, MinIndex) :-
   % dynamic ordering by offset
   predsort(b_sort([offset-(<), index-(<)]), Buffers, Sorted),
   % maplist([B]>>(b_id(B, Id), b_offset(B, Offset), format("dynamic ordering: ~p, ~p~n", [Id, Offset])), Sorted),
   min_height(Sorted, MinHeight),
   % format("min height: ~p~n", [MinHeight]),
   select(Buffer, Sorted, Rest),
   % print_term(Buffer, []), nl,
   % canonical solutions only
   b_offset(Buffer, Offset),
   % b_id(Buffer, Id),
   % format("~p,~p~n", [Id, Offset]),
   % (  Id == 19
   % -> gtrace
   % ;  true
   % ),
   Offset >= MinOffset,
   b_index(Buffer, Index),
   (  Offset == MinOffset
   -> Index >= MinIndex
   ;  true
   ),
   % dominance check
   Offset < MinHeight,
   % I want to apply Offset to Buffer, what do I need to update ?
   % update the minimum offset and height of any overlapping buffer
   % update the floor, total, u and s of any section overlapping Buffer
   % and assert that floor + total =< C
   maplist(section_inference(Buffer, C), Sections, Sections1),
   % gtrace,
   % maplist(verify_section, Sections1),
   sections_partitions(Sections1, Partitions),
   % maplist(verify_section, Sections1),
   (  Partitions = [NewSections]
   -> inference(Rest, NewSections, C, Heuristic, Offset, Index)
   ;  maplist(partition_inference(C, Heuristic), Partitions)
   ).

verify_section(X) :-
   section_floor(X, Floor),
   section_total(X, Total),
   section_u(X, U),
   maplist(b_size, U, Sizes),
   sum_list(Sizes, Total1),
   (  Total == Total1
   -> true
   ;  gtrace
   ),
   % section_s(X, S),
   % maplist(b_height, S, Heights),
   % (  Heights = []
   % -> Floor1 = 0
   % ;  max_list(Heights, Floor1)
   % ),
   % (  Floor \== 0
   % -> true
   % ;  gtrace
   % ),
   format("check ~p ~p~n", [Floor, Total]).
   
section_inference(Buffer, C, X, X2) :-
   section_u(X, U),
   section_total(X, Total),
   section_floor(X, Floor),
   % (  Floor == 66560, Total == 155648
   % -> gtrace
   % ;  true
   % ),
   (  ord_memberchk(Buffer, U)
   -> ord_del_element(U, Buffer, U1),
      maplist(update_buffer(Buffer), U1),

      section_s(X, S),
      ord_add_element(S, Buffer, S1),

      b_size(Buffer, Size),
      Total1 is Total - Size,
      % format("total ~p~n", [Total2]),
      b_height(Buffer, Height),
      Floor1 is max(Floor, Height),
      set_section_fields([u(U1), s(S1), total(Total1), floor(Floor1)], X, X1)
   ;  X1 = X, Total1 = Total, Floor1 = Floor
   ),


   b_offset(Buffer, Offset),
   % monotonic floor
   % Floor2 is max(Floor1, Offset),
   MonotonicFloor is max(Floor1, Offset),

   maplist(b_offset, U, Offsets),
   (  Offsets = []
   -> EffectiveHeight = 0
   ;  % effective height
      min_list(Offsets, EffectiveHeight)
   ),
   Floor2 is max(MonotonicFloor, EffectiveHeight),
   set_floor_of_section(Floor2, X1, X2),

   % format("floor ~p~n", [Floor2]),

   % (  max(Offset, Floor2) + Total2 > C
   % -> gtrace
   % ;  true
   % ),
   % max(EffectiveHeight, (Floor2 + Total1)) =< C.
   Floor2 + Total1 =< C.


update_buffer(B1, B2) :-
   (  overlap(B1, B2)
   -> % overlapping buffer
      b_height(B1, MinHeight)
   ;  % offset monotonicity
      % b_offset(B1, MinHeight)
      MinHeight = 0
   ),
   b_offset(B2, O2),
   (  MinHeight > O2
   -> set_offset_of_b(MinHeight, B2),
      b_size(B2, Size2),
      H2 is MinHeight + Size2,
      set_height_of_b(H2, B2)
   ;  true
   ).

minimalloc(Buffers) :-
   minimalloc(Buffers, []).
minimalloc(Buffers, Options) :-
   option(capacity(C), Options, 1048576),
   option(heuristics(Hs), Options, [
      [width-(>), area-(>), total-(>), id-(<)],
      [total-(>), area-(>), width-(>), id-(<)],
      [total-(>), width-(>), area-(>), id-(<)]
   ]),
   option(limit(Limit), Options, 33554432),
   buffers_partitions(Buffers, Partitions),
   round_robin(Hs, C, Limit, Partitions),
   (  option(validate(true), Options)
   -> time(validate_solution(Buffers))
   ;  true
   ).

b_rect(Buffer, rect(Low, Width, Offset, Size)) :-
   b_low(Buffer, Low),
   b_width(Buffer, Width),
   b_offset(Buffer, Offset),
   b_size(Buffer, Size).

validate_solution(Buffers) :-
   maplist(b_rect, Buffers, Rects),
   disjoint2(Rects).

print_solution(Buffers) :-
   maplist(b_id, Buffers, Ids),
   maplist(b_offset, Buffers, Offset),
   transpose([Ids, Offset], L),
   print_term(L, []).

b_row(B, row(Id, Low, Upper, Size, Offset)) :-
   b_id(B, Id),
   b_low(B, Low),
   b_upper(B, Upper),
   b_size(B, Size),
   b_offset(B, Offset).

write_solutions(Buffers, File) :-
   maplist(b_row, Buffers, Rows),
   csv_write_file(File, [row(id, lower, upper, size, offset) | Rows]).

:- begin_tests(minimalloc).
:- set_test_options([format(log)]).

challenging("C.1048576.csv", [
   limit(586870912), check("C.1048576.out.csv"),
   heuristics([[total-(>), area-(>), width-(>), id-(<)]])], 40).
challenging("K.1048576.csv", [check("K.1048576.out.csv")], 10).
challenging("A.1048576.csv", [head(140)], 10).
challenging("B.1048576.csv", [head(150)], 10).
challenging("D.1048576.csv", [head(190)], 10).
challenging("E.1048576.csv", [head(180)], 10).
challenging("F.1048576.csv", [head(250)], 10).
challenging("G.1048576.csv", [head(270)], 10).
challenging("H.1048576.csv", [head(280)], 10).
challenging("I.1048576.csv", [head(280)], 10).
challenging("J.1048576.csv", [head(280)], 10).

test(challenging, [forall(challenging(File, Options, Timeout))]) :-
   rows(File, Buffers, Options),
   call_with_time_limit(Timeout, time(minimalloc(Buffers, Options))),
   (  option(check(Out), Options)
   -> csv_read_file(Out, [_Header | Rows]),
      maplist(arg(5), Rows, TrueOffsets),
      maplist(b_offset, Buffers, PredOffsets),
      TrueOffsets == PredOffsets
   ;  true
   ).

:- end_tests(minimalloc).
