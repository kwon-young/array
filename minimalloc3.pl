:- use_module(library(record)).
:- use_module(library(heaps)).
:- use_module(library(macros)).
:- use_module(library(csv)).
:- use_module(library(yall)).

:- record buffer(offset, index, id, static, height, size, start, end).
:- record wat(width, area, total, id).
:- record taw(total, area, width, id).
:- record twa(total, width, area, id).
:- record section(id, floor, total, buffers, end).

#define(offset, 1).
#define(id, 3).
#define(static, 4).
#define(height, 5).

rows(File, Rows) :-
   rows(File, Rows, []).

rows(File, Rows, Options) :-
   csv_read_file(File, [_Header | AllRows]),
   maplist(add_offset, AllRows, RowsOffset),
   (  option(head(Head), Options)
   -> length(Rows, Head),
      append(Rows, _, RowsOffset)
   ;  Rows = RowsOffset
   ).

add_offset(row(Id, Start, End, Size), row(Id, Start, End, Size, _Offset)).
add_offset(row(Id, Start, End, Size, Offset), row(Id, Start, End, Size, Offset)).

row_buffer(Id, row(_, Start, End, Size, _), Buffer) :-
   make_buffer([id(Id), start(Start), end(End), size(Size), offset(0),
                height(Size), index(Id)], Buffer).

buffer_allocated_offset(Buffer, Offset) :-
   buffer_offset(Buffer, allocated(Offset)).
row_offset(row(_, _, _, _, Offset), Offset).

min_height(Buffers, MinHeight) :-
   sort(#height, @<, Buffers, [B | _]),
   buffer_height(B, MinHeight).

min_offset_buffer(Buffer, Buffers, Rest) :-
   sort(Buffers, [Buffer | Rest]).

allocate_buffer(C, Buffer, Overlaps, Sections, SectionList) :-
   buffer_offset(Buffer, Offset),
   set_offset_of_buffer(allocated(Offset), Buffer),
   buffer_height(Buffer, Height),
   set_height_of_buffer(allocated(Height), Buffer),
   buffer_id(Buffer, Id),
   arg(Id, Sections, BufferSections),
   arg(Id, Overlaps, BufferOverlaps),
   % could be done with a foldl, but hot code path, avoid meta predicate
   update_buffer(BufferOverlaps, Height, Sections, [], AffectedSections),
   buffer_size(Buffer, Size),
   maplist(update_section_floor(Buffer, Height, Size), BufferSections),
   update_sections(AffectedSections),
   maplist(check_section(C, Offset), SectionList).

update_buffer([], _, _, Sections, Sections).
update_buffer([B2 | Bs], Height1, Sections, Sections1, Sections3) :-
   buffer_offset(B2, Offset2),
   (  integer(Offset2), Offset2 < Height1
   -> buffer_size(B2, Size2),
      NewHeight2 is Height1 + Size2,
      set_offset_of_buffer(Height1, B2),
      set_height_of_buffer(NewHeight2, B2),
      buffer_id(B2, Id),
      arg(Id, Sections, B2Sections),
      ord_union(Sections1, B2Sections, Sections2)
      % maplist(section_id, Sections2, SectionIds),
      % (  memberchk(215, SectionIds)
      % -> gtrace
      % ;  true
      % )
   ;  Sections2 = Sections1
   ),
   update_buffer(Bs, Height1, Sections, Sections2, Sections3).
   
update_section_floor(Buffer, Height, Size, Section) :-
   % (  section_id(Section, 38)
   % -> gtrace
   % ;  true
   % ),
   section_total(Section, Total1),
   Total2 is Total1 - Size,
   set_floor_of_section(Height, Section),
   set_total_of_section(Total2, Section),
   section_buffers(Section, Buffers1),
   ord_del_element(Buffers1, Buffer, Buffers2),
   set_buffers_of_section(Buffers2, Section).

effective_height([], Min, Min).
effective_height([Buffer | Buffers], Min1, Min3) :-
   % hottest code path, avoid extra predicate call
   Buffer = buffer(Offset, _, _, _, _, _, _, _),
   % buffer_offset(Buffer, Offset),
   Min2 is min(Min1, Offset),
   effective_height(Buffers, Min2, Min3).

update_sections([]).
update_sections([Section | Sections]) :-
   % hot code path, avoid extra predicate call
   Section = section(_, Floor1, _, Buffers, _),
   % section_floor(Section, Floor1),
   % section_buffers(Section, Buffers),
   effective_height(Buffers, inf, MinOffset),
   (  MinOffset \== inf, Floor1 < MinOffset
   -> set_floor_of_section(MinOffset, Section)
   ;  true
   ),
   update_sections(Sections).

check_section(C, Offset, Section) :-
   section_floor(Section, Floor),
   section_total(Section, Total),
   % section_id(Section, Id),
   % format("section: ~p,~p,~p~n", [Id, Floor, Offset]),
   max(Offset, Floor) + Total =< C,
   !.
% check_section(C, Offset, Section) :-
%    gtrace,
%    print_term([C, Offset, Section], []).

update_cuts(Buffer, AllCuts, SortedCuts) :-
   buffer_id(Buffer, Id),
   arg(Id, AllCuts, Cuts),
   foldl(update_cut, Cuts, ZeroCuts, []),
   sort(ZeroCuts, SortedCuts).

update_cut(Cut, ZeroCuts1, ZeroCuts2) :-
   Cut = cut(N, V),
   N1 is N - 1,
   setarg(1, Cut, N1),
   (  N1 == 0
   -> ZeroCuts1 = [V | ZeroCuts2]
   ;  ZeroCuts1 = ZeroCuts2
   ).

inference(Heuristic, C, Overlaps, Sections, SectionList, Cuts, Buffers0, MinOffset, MinIndex) :-
   min_height(Buffers0, MinHeight),
   sort(Buffers0, Sorted),
   % maplist([B]>>(
   %    buffer_id(B, Id),
   %    buffer_offset(B, Offset),
   %    format("sorted: ~p,~p~n", [Id, Offset])), Sorted),
   select(Buffer, Sorted, Buffers1),
   % nb_getval(inference, Count),
   % Count1 is Count + 1,
   % nb_setval(inference, Count1),
   buffer_offset(Buffer, Offset),
   % buffer_id(Buffer, Id),
   % format("~p,~p,~p~n", [Id, Offset,Count1]),
   % (  Count1 == 7
   % -> gtrace
   % ;  true
   % ),
   Offset >= MinOffset,
   buffer_index(Buffer, Index),
   (  Offset == MinOffset
   -> Index >= MinIndex
   ;  true
   ),
   Offset < MinHeight,
   allocate_buffer(C, Buffer, Overlaps, Sections, SectionList),
   update_cuts(Buffer, Cuts, ZeroCuts),
   (  Buffers1 == []
   -> true
   ;  ZeroCuts == []
   -> inference(Heuristic, C, Overlaps, Sections, SectionList, Cuts, Buffers1, Offset, Index)
   ;  append(ZeroCuts, [inf], ZeroCutsInf),
      foldl(partition_inference(Heuristic, C, Overlaps, Sections, Cuts),
            ZeroCutsInf, SectionList-Buffers1, []-[])
   ).

left(Cut, Buffer), default_buffer(Buffer) =>
   buffer_end(Buffer, End),
   End =< Cut.
left(Cut, Section), default_section(Section) =>
   section_end(Section, End),
   End =< Cut.

partition_inference(Heuristic, C, Overlaps, Sections, Cuts, ZeroCut,
                    SectionList-Buffers, RightSections-RightBuffers) :-
   partition(left(ZeroCut), Buffers, LeftBuffers, RightBuffers),
   partition(left(ZeroCut), SectionList, LeftSections, RightSections),

   (  LeftBuffers = []
   -> true
   ;  length(LeftBuffers, N),
      maplist(buffer_heuristic(N, Heuristic, Sections), LeftBuffers),

      % sort(#id, @=<, LeftBuffers, IdSortBuffers),
      % maplist([B]>>(buffer_id(B, Id), buffer_static(B, twa(Total, _, _, _)),
      %               format("prestatic: ~p,~p~n", [Id, Total])), LeftBuffers),

      sort(#static, @>=, LeftBuffers, SortedBuffers),

      % maplist([B]>>(
      %    buffer_id(B, Id),
      %    buffer_static(B, twa(Total, _, _, _)),
      %    format("static: ~p,~p~n", [Id, Total])), SortedBuffers),

      numlist(1, N, Index),
      maplist(set_index_of_buffer, Index, SortedBuffers),
      once(inference(Heuristic, C, Overlaps, Sections, LeftSections, Cuts, SortedBuffers, 0, 0))
   ).

buffers_overlaps(Buffers, Compound) :-
   list_to_ord_set(Buffers, Set),
   maplist(buffer_overlaps(Set), Buffers, Overlaps),
   compound_name_arguments(Compound, overlaps, Overlaps).

buffer_overlaps(Buffers, Buffer, Overlaps) :-
   include(overlap(Buffer), Buffers, AllOverlaps),
   ord_del_element(AllOverlaps, Buffer, Overlaps).

buffers_cuts(Buffers, Compound, ZeroCuts) :-
   maplist(buffer_end, Buffers, Ends),
   sort(Ends, SortedEnds),
   once(append(Cuts, [_], SortedEnds)),
   maplist(buffers_cut(Buffers), Cuts, PPairs),
   maplist([V, Pairs, cut(N, V)]>>length(Pairs, N), Cuts, PPairs, CutList),
   convlist([cut(0, V), V]>>true, CutList, ZeroCuts),
   append(PPairs, Pairs),
   keysort(Pairs, SortedPairs),
   group_pairs_by_key(SortedPairs, Groups),
   same_length(Buffers, Args),
   compound_name_arguments(Compound, cuts, Args),
   maplist({Compound}/[Id-BufferCuts]>>arg(Id, Compound, BufferCuts), Groups),
   maplist([Arg]>>once(length(Arg, _)), Args).

buffers_cut(Buffers, Cut, Pairs) :-
   include(inside(Cut), Buffers, Inside),
   length(Inside, N),
   maplist(buffer_id, Inside, Ids),
   Compound = cut(N, Cut),
   maplist({Compound}/[Id, Id-Compound]>>true, Ids, Pairs).

inside(Point, B) :-
   buffer_start(B, L),
   buffer_end(B, U),
   L < Point, Point < U.

buffers_sections(Buffers, SectionList, Compound) :-
   maplist(buffer_end, Buffers, Ends),
   sort(Ends, Cuts),
   length(Cuts, N),
   numlist(1, N, Ids),
   foldl(buffers_section(Buffers), Ids, SectionList, Cuts, -inf, _),
   maplist(buffer_sections(SectionList), Buffers, Sections),
   compound_name_arguments(Compound, sections, Sections).

buffers_section(Buffers, Id, Section, End, Start, End) :-
   include(overlap(Start, End), Buffers, SectionBuffers),
   list_to_ord_set(SectionBuffers, Set),
   maplist(buffer_size, SectionBuffers, Sizes),
   sum_list(Sizes, Total),
   make_section([id(Id), floor(0), total(Total), buffers(Set), end(End)], Section).

buffer_sections(SectionList, Buffer, Sections) :-
   include(buffer_section(Buffer), SectionList, Sections).

buffer_section(Buffer, Section) :-
   section_buffers(Section, Buffers),
   memberchk(Buffer, Buffers).

overlap(L1, U1, B2) :-
   buffer_start(B2, L2),
   buffer_end(B2, U2),
   U1 > L2, L1 < U2.

overlap(B1, B2) :-
   buffer_start(B1, L1),
   buffer_end(B1, U1),
   buffer_start(B2, L2),
   buffer_end(B2, U2),
   U1 > L2, L1 < U2.

heuristic(C, Overlaps, Sections, SectionList, Cuts, ZeroCuts, Buffers, Offsets, Heuristic) :-
   debug(heuristic, "heuristic called with ~p~n", [Heuristic]),
   % length(Buffers, N),
   % maplist(buffer_heuristic(N, Heuristic, Sections), Buffers),
   append(ZeroCuts, [inf], ZeroCutsInf),
   foldl(partition_inference(Heuristic, C, Overlaps, Sections, Cuts),
         ZeroCutsInf, SectionList-Buffers, []-[]),
   maplist(buffer_allocated_offset, Buffers, Offsets),
   debug(heuristic, "heuristic ~p: found solution ~p~n", [Heuristic, Offsets]).

buffer_heuristic(N, Heuristic, Sections, Buffer) :-
   atom_concat('make_', Heuristic, Goal),
   buffer_id(Buffer, Id),
   Id1 is N - Id,
   buffer_start(Buffer, Start),
   buffer_end(Buffer, End),
   buffer_size(Buffer, Size),
   Width is End - Start,
   Area is Width * Size,
   arg(Id, Sections, BufferSections),
   maplist(section_total, BufferSections, Totals),
   max_list(Totals, Total),
   call(Goal, [id(Id1), width(Width), area(Area), total(Total)], Static),
   set_static_of_buffer(Static, Buffer).

minimalloc(Rows) :-
   minimalloc(Rows, []).

minimalloc(Rows, Options) :-
   length(Rows, N),
   numlist(1, N, Ids),
   maplist(row_buffer, Ids, Rows, Buffers),
   buffers_overlaps(Buffers, Overlaps),
   buffers_cuts(Buffers, Cuts, ZeroCuts),
   buffers_sections(Buffers, SectionList, Sections),
   option(capacity(C), Options, 1048576),
   option(heuristics(Heuristics), Options, [wat, taw, twa]),
   Goal = heuristic(C, Overlaps, Sections, SectionList, Cuts, ZeroCuts, Buffers, Offsets),
   (  Heuristics = [Heuristic]
   -> call(Goal, Heuristic)
   ;  maplist({Goal}/[H, call(Goal, H)]>>true, Heuristics, Goals),
      first_solution(Offsets, Goals, [])
   ),
   maplist(row_offset, Rows, Offsets).

challenging(File) :-
   code_type(C, upper),
   C =< 0'K,
   append([C], `.1048576.csv`, File).

benchmark :-
   findall(File, challenging(File), Files),
   maplist(rows, Files, Rows),
   maplist([File, Row]>>(
      call_time(minimalloc(Row), Time),
      get_dict(wall, Time, Wall),
      format("~s: ~3f seconds~n", [File, Wall])), Files, Rows).

row_rect(row(_, Start, End, Size, Offset), rect(Start, Width, Offset, Size)) :-
   Width is End - Start.

:- begin_tests(minimalloc).

test(input12) :-
   rows("input.12.csv", Rows, []),
   minimalloc(Rows, [capacity(12), heuristics([wat])]).

test(challenging, [forall(challenging(File))]) :-
   rows(File, Rows, []),
   minimalloc(Rows, []).


:- end_tests(minimalloc).
