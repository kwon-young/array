:- use_module(library(record)).
:- use_module(library(heaps)).
:- use_module(library(macros)).
:- use_module(library(csv)).

:- record buffer(offset, index, id, static, height, size, start, end).
:- record wat(width, area, total, id).
:- record taw(total, area, width, id).
:- record twa(total, width, area, id).
:- record section(id, floor, total, offsets).

#define(offset, 1).
#define(static, 4).
#define(height, 5).

ord_replace(Set1, X1, Set2, X2) :-
   ord_del_element(Set1, X1, Set),
   ord_add_element(Set, X2, Set2).

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
   maplist(update_buffer(Height, Sections), BufferOverlaps),
   buffer_size(Buffer, Size),
   maplist(update_section_floor(Offset-Id, Height, Size), BufferSections),
   maplist(check_section(C, Offset), SectionList).

update_buffer(Height1, Sections, B2) :-
   buffer_offset(B2, Offset2),
   (  integer(Offset2), Offset2 < Height1
   -> buffer_size(B2, Size2),
      NewHeight2 is Height1 + Size2,
      set_offset_of_buffer(Height1, B2),
      set_height_of_buffer(NewHeight2, B2),
      buffer_id(B2, Id),
      arg(Id, Sections, B2Sections),
      maplist(update_section(Offset2-Id, Height1-Id), B2Sections)
   ;  true
   ).
   
update_section_floor(Offset, Height, Size, Section) :-
   % (  section_id(Section, 10)
   % -> gtrace
   % ;  true
   % ),
   section_total(Section, Total1),
   Total2 is Total1 - Size,
   set_floor_of_section(Height, Section),
   set_total_of_section(Total2, Section),
   section_offsets(Section, Offsets1),
   % (  ord_memberchk(Offset, Offsets1)
   % -> true
   % ;  gtrace
   % ),
   ord_del_element(Offsets1, Offset, Offsets2),
   set_offsets_of_section(Offsets2, Section).

update_section(Old, New, Section) :-
   section_offsets(Section, Offsets1),
   ord_replace(Offsets1, Old, Offsets2, New),
   set_offsets_of_section(Offsets2, Section).

check_section(C, Offset, Section) :-
   % (  section_id(Section, 10)
   % -> gtrace
   % ;  true
   % ),
   section_floor(Section, Floor1),
   (  section_offsets(Section, [MinOffset-_ | _]),
      Floor1 < MinOffset
   -> set_floor_of_section(MinOffset, Section)
   ;  true
   ),
   section_floor(Section, Floor),
   section_total(Section, Total),
   % section_id(Section, Id),
   % format("section ~p,~p~n", [Id, Floor]),
   max(Offset, Floor) + Total =< C.

update_cuts(Buffer, AllCuts, ZeroCuts) :-
   buffer_id(Buffer, Id),
   arg(Id, AllCuts, Cuts),
   foldl(update_cut, Cuts, ZeroCuts, []).

update_cut(Cut, ZeroCuts1, ZeroCuts2) :-
   Cut = cut(N, V),
   N1 is N - 1,
   setarg(1, Cut, N1),
   (  N1 == 0
   -> ZeroCuts1 = [V | ZeroCuts2]
   ;  ZeroCuts1 = ZeroCuts2
   ).

inference(C, Overlaps, Sections, SectionList, Cuts, Buffers0, MinOffset, MinIndex) :-
   min_height(Buffers0, MinHeight),
   sort(Buffers0, Sorted),
   select(Buffer, Sorted, Buffers1),
   buffer_offset(Buffer, Offset),
   % buffer_id(Buffer, Id),
   % (  Id == 47; Id == 198
   % -> gtrace
   % ;  true
   % ),
   % format("~p,~p~n", [Id, Offset]),
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
   -> inference(C, Overlaps, Sections, SectionList, Cuts, Buffers1, Offset, Index)
   ;  append(ZeroCuts, [inf], ZeroCutsInf),
      foldl(partition_inference(C, Overlaps, Sections, SectionList, Cuts), ZeroCutsInf, Buffers1, [])
   ).

left(Cut, Buffer) :-
   buffer_end(Buffer, End),
   End =< Cut.

partition_inference(C, Overlaps, Sections, SectionList, Cuts, ZeroCut,
                    Buffers, RightBuffers) :-
   partition(left(ZeroCut), Buffers, LeftBuffers, RightBuffers),
   sort(#static, @>=, LeftBuffers, SortedBuffers),
   length(SortedBuffers, N),
   numlist(1, N, Index),
   maplist(set_index_of_buffer, Index, SortedBuffers),
   once(inference(C, Overlaps, Sections, SectionList, Cuts, SortedBuffers, 0, 0)).

buffers_overlaps(Buffers, Compound) :-
   list_to_ord_set(Buffers, Set),
   maplist(buffer_overlaps(Set), Buffers, Overlaps),
   compound_name_arguments(Compound, overlaps, Overlaps).

buffer_overlaps(Buffers, Buffer, Overlaps) :-
   include(overlap(Buffer), Buffers, AllOverlaps),
   ord_del_element(AllOverlaps, Buffer, Overlaps).

buffers_cuts(Buffers, Compound) :-
   maplist(buffer_end, Buffers, Ends),
   sort(Ends, SortedEnds),
   once(append(Cuts, [_], SortedEnds)),
   maplist(buffers_cut(Buffers), Cuts, PPairs),
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
   maplist({N, Cut}/[Id, Id-cut(N, Cut)]>>true, Ids, Pairs).

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
   maplist([B, Offset-Id]>>(buffer_offset(B, Offset), buffer_id(B, Id)),
           SectionBuffers, Offsets),
   maplist(buffer_size, SectionBuffers, Sizes),
   sum_list(Sizes, Total),
   make_section([id(Id), floor(0), total(Total), offsets(Offsets)], Section).

buffer_sections(SectionList, Buffer, Sections) :-
   include(buffer_section(Buffer), SectionList, Sections).

buffer_section(Buffer, Section) :-
   buffer_id(Buffer, Id),
   section_offsets(Section, Offsets),
   memberchk(_-Id, Offsets).

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

heuristic(C, Overlaps, Sections, SectionList, Cuts, Buffers, Offsets, Heuristic) :-
   debug(heuristic, "heuristic called with ~p~n", [Heuristic]),
   length(Buffers, N),
   maplist(buffer_heuristic(N, Heuristic, Sections), Buffers),
   time(partition_inference(C, Overlaps, Sections, SectionList, Cuts, inf, Buffers, [])),
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
   buffer_static(Buffer, Static).

minimalloc(Rows, Options) :-
   length(Rows, N),
   numlist(1, N, Ids),
   maplist(row_buffer, Ids, Rows, Buffers),
   buffers_overlaps(Buffers, Overlaps),
   buffers_cuts(Buffers, Cuts),
   buffers_sections(Buffers, SectionList, Sections),
   option(capacity(C), Options, 1048576),
   option(heuristics(Heuristics), Options, [wat, taw, twa]),
   (  Heuristics = [Heuristic]
   -> heuristic(C, Overlaps, Sections, SectionList, Cuts, Buffers, Offsets, Heuristic)
   ;  Heuristic = heuristic(C, Overlaps, Sections, SectionList, Cuts, Buffers, Offsets),
      maplist({Heuristic}/[H, call(Heuristic, H)]>>true, Heuristics, Goals),
      first_solution(Offsets, Goals, [])
   ),
   maplist(row_offset, Rows, Offsets).

:- begin_tests(minimalloc).

test(input12) :-
   rows("input.12.out.csv", Rows, []),
   minimalloc(Rows, [capacity(12), heuristics([wat])]).

:- end_tests(minimalloc).
