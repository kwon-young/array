:- use_module(library(record)).
:- use_module(library(heaps)).
:- use_module(library(macros)).
:- use_module(library(csv)).
:- use_module(library(yall)).

:- record buffer(id, start, end, size, offset).
:- record b(offset, index, id, static, height, size, start, end).
:- record wat(width, area, total, id).
:- record taw(total, area, width, id).
:- record twa(total, width, area, id).
:- record section(id, floor, total, bs, end).

#define(offset, 1).
#define(id, 3).
#define(static, 4).
#define(height, 5).

csv_read_buffers(File, Buffers) :-
   csv_read_buffers(File, Buffers, []).

csv_read_buffers(File, Buffers, Options) :-
   csv_read_file(File, [_Header | AllRows], [functor(buffer)]),
   maplist(add_offset, AllRows, AllBuffers),
   (  option(head(Head), Options)
   -> length(Buffers, Head),
      append(Buffers, _, AllBuffers)
   ;  Buffers = AllBuffers
   ).

add_offset(buffer(Id, Start, End, Size), buffer(Id, Start, End, Size, _Offset)).
add_offset(buffer(Id, Start, End, Size, Offset), buffer(Id, Start, End, Size, Offset)).

buffer_b(Id, Buffer, B) :-
   buffer_start(Buffer, Start),
   buffer_end(Buffer, End),
   buffer_size(Buffer, Size),
   make_b([id(Id), start(Start), end(End), size(Size), offset(0), height(Size),
           index(Id)], B).

b_allocated_offset(B, Offset) :-
   b_offset(B, allocated(Offset)).

min_height(Bs, MinHeight) :-
   sort(#height, @<, Bs, [B | _]),
   b_height(B, MinHeight).

allocate_b(C, B, Overlaps, Sections, SectionList) :-
   b_offset(B, Offset),
   set_offset_of_b(allocated(Offset), B),
   b_height(B, Height),
   set_height_of_b(allocated(Height), B),
   b_id(B, Id),
   arg(Id, Sections, BSections),
   arg(Id, Overlaps, BOverlaps),
   % could be done with a foldl, but hot code path, avoid meta predicate
   update_b(BOverlaps, Height, Sections, [], AffectedSections),
   b_size(B, Size),
   maplist(update_section_floor(B, Height, Size), BSections),
   update_sections(AffectedSections),
   maplist(check_section(C, Offset), SectionList).

update_b([], _, _, Sections, Sections).
update_b([B2 | Bs], Height1, Sections, Sections1, Sections3) :-
   b_offset(B2, Offset2),
   (  integer(Offset2), Offset2 < Height1
   -> b_size(B2, Size2),
      NewHeight2 is Height1 + Size2,
      set_offset_of_b(Height1, B2),
      set_height_of_b(NewHeight2, B2),
      b_id(B2, Id),
      arg(Id, Sections, B2Sections),
      ord_union(Sections1, B2Sections, Sections2)
   ;  Sections2 = Sections1
   ),
   update_b(Bs, Height1, Sections, Sections2, Sections3).
   
update_section_floor(B, Height, Size, Section) :-
   section_total(Section, Total1),
   Total2 is Total1 - Size,
   set_floor_of_section(Height, Section),
   set_total_of_section(Total2, Section),
   section_bs(Section, Bs1),
   ord_del_element(Bs1, B, Bs2),
   set_bs_of_section(Bs2, Section).

effective_height([], Min, Min).
effective_height([B | Bs], Min1, Min3) :-
   % hottest code path, avoid extra predicate call
   B = b(Offset, _, _, _, _, _, _, _),
   % b_offset(B, Offset),
   Min2 is min(Min1, Offset),
   effective_height(Bs, Min2, Min3).

update_sections([]).
update_sections([Section | Sections]) :-
   % hot code path, avoid extra predicate call
   Section = section(_, Floor1, _, Bs, _),
   % section_floor(Section, Floor1),
   % section_bs(Section, Bs),
   effective_height(Bs, inf, MinOffset),
   (  MinOffset \== inf, Floor1 < MinOffset
   -> set_floor_of_section(MinOffset, Section)
   ;  true
   ),
   update_sections(Sections).

check_section(C, Offset, Section) :-
   section_floor(Section, Floor),
   section_total(Section, Total),
   max(Offset, Floor) + Total =< C.

update_cuts(B, AllCuts, SortedCuts) :-
   b_id(B, Id),
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

inference(Heuristic, C, Overlaps, Sections, SectionList, Cuts, Bs0, MinOffset, MinIndex) :-
   min_height(Bs0, MinHeight),
   sort(Bs0, Sorted),
   select(B, Sorted, Bs1),
   % offset and index monotonicity
   b_offset(B, Offset),
   Offset >= MinOffset,
   b_index(B, Index),
   (  Offset == MinOffset
   -> Index >= MinIndex
   ;  true
   ),
   % dominance check
   Offset < MinHeight,

   allocate_b(C, B, Overlaps, Sections, SectionList),

   update_cuts(B, Cuts, ZeroCuts),
   (  Bs1 == []
   -> true
   ;  ZeroCuts == []
   -> inference(Heuristic, C, Overlaps, Sections, SectionList, Cuts, Bs1, Offset, Index)
   ;  append(ZeroCuts, [inf], ZeroCutsInf),
      foldl(partition_inference(Heuristic, C, Overlaps, Sections, Cuts),
            ZeroCutsInf, SectionList-Bs1, []-[])
   ).

left_b(Cut, B) :-
   b_end(B, End),
   End =< Cut.
left_section(Cut, Section) :-
   section_end(Section, End),
   End =< Cut.

partition_inference(Heuristic, C, Overlaps, Sections, Cuts, ZeroCut,
                    SectionList-Bs, RightSections-RightBs) :-
   partition(left_b(ZeroCut), Bs, LeftBs, RightBs),
   partition(left_section(ZeroCut), SectionList, LeftSections, RightSections),

   (  LeftBs = []
   -> true
   ;  length(LeftBs, N),
      maplist(update_static_of_b(N, Heuristic, Sections), LeftBs),

      sort(#static, @>=, LeftBs, SortedBs),

      numlist(1, N, Index),
      maplist(set_index_of_b, Index, SortedBs),
      once(inference(Heuristic, C, Overlaps, Sections, LeftSections, Cuts, SortedBs, 0, 0))
   ).

update_static_of_b(N, Heuristic, Sections, B) :-
   b_id(B, Id),
   % need to reverse the order of Id, since sorting will be done at the
   % compound level in partition_inference with @>= order and we want to
   % keep the original ascending Id ordering
   Id1 is N - Id,
   b_start(B, Start),
   b_end(B, End),
   b_size(B, Size),
   Width is End - Start,
   Area is Width * Size,
   arg(Id, Sections, BSections),
   maplist(section_total, BSections, Totals),
   max_list(Totals, Total),
   atom_concat('make_', Heuristic, Goal),
   call(Goal, [id(Id1), width(Width), area(Area), total(Total)], Static),
   set_static_of_b(Static, B).

bs_overlaps(Bs, Compound) :-
   list_to_ord_set(Bs, Set),
   maplist(b_overlaps(Set), Bs, Overlaps),
   compound_name_arguments(Compound, overlaps, Overlaps).

b_overlaps(Bs, B, Overlaps) :-
   include(overlap(B), Bs, AllOverlaps),
   ord_del_element(AllOverlaps, B, Overlaps).

bs_cuts(Bs, Compound, ZeroCuts) :-
   maplist(b_end, Bs, Ends),
   sort(Ends, SortedEnds),
   once(append(Cuts, [_], SortedEnds)),
   maplist(bs_cut(Bs), Cuts, PPairs),
   maplist([V, Pairs, cut(N, V)]>>length(Pairs, N), Cuts, PPairs, CutList),
   convlist([cut(0, V), V]>>true, CutList, ZeroCuts),
   append(PPairs, Pairs),
   keysort(Pairs, SortedPairs),
   group_pairs_by_key(SortedPairs, Groups),
   same_length(Bs, Args),
   compound_name_arguments(Compound, cuts, Args),
   maplist({Compound}/[Id-BCuts]>>arg(Id, Compound, BCuts), Groups),
   maplist([Arg]>>once(length(Arg, _)), Args).

bs_cut(Bs, Cut, Pairs) :-
   include(inside(Cut), Bs, Inside),
   length(Inside, N),
   maplist(b_id, Inside, Ids),
   Compound = cut(N, Cut),
   maplist({Compound}/[Id, Id-Compound]>>true, Ids, Pairs).

inside(Point, B) :-
   b_start(B, L),
   b_end(B, U),
   L < Point, Point < U.

bs_sections(Bs, SectionList, Compound) :-
   maplist(b_end, Bs, Ends),
   sort(Ends, Cuts),
   length(Cuts, N),
   numlist(1, N, Ids),
   foldl(bs_section(Bs), Ids, SectionList, Cuts, -inf, _),
   maplist(b_sections(SectionList), Bs, Sections),
   compound_name_arguments(Compound, sections, Sections).

bs_section(Bs, Id, Section, End, Start, End) :-
   include(overlap(Start, End), Bs, SectionBs),
   list_to_ord_set(SectionBs, Set),
   maplist(b_size, SectionBs, Sizes),
   sum_list(Sizes, Total),
   make_section([id(Id), floor(0), total(Total), bs(Set), end(End)], Section).

b_sections(SectionList, B, Sections) :-
   include(b_section(B), SectionList, Sections).

b_section(B, Section) :-
   section_bs(Section, Bs),
   memberchk(B, Bs).

overlap(L1, U1, B2) :-
   b_start(B2, L2),
   b_end(B2, U2),
   U1 > L2, L1 < U2.

overlap(B1, B2) :-
   b_start(B1, L1),
   b_end(B1, U1),
   b_start(B2, L2),
   b_end(B2, U2),
   U1 > L2, L1 < U2.

heuristic(C, Overlaps, Sections, SectionList, Cuts, ZeroCuts, Bs, Offsets, Heuristic) :-
   debug(heuristic, "heuristic called with ~p~n", [Heuristic]),
   append(ZeroCuts, [inf], ZeroCutsInf),
   foldl(partition_inference(Heuristic, C, Overlaps, Sections, Cuts),
         ZeroCutsInf, SectionList-Bs, []-[]),
   maplist(b_allocated_offset, Bs, Offsets),
   debug(heuristic, "heuristic ~p found solution~n", [Heuristic]).

minimalloc(Buffers) :-
   minimalloc(Buffers, []).

minimalloc(Buffers, Options) :-
   length(Buffers, N),
   numlist(1, N, Ids),
   maplist(buffer_b, Ids, Buffers, Bs),
   bs_overlaps(Bs, Overlaps),
   bs_cuts(Bs, Cuts, ZeroCuts),
   bs_sections(Bs, SectionList, Sections),
   option(capacity(C), Options, 1048576),
   option(heuristics(Heuristics), Options, [wat, taw, twa]),
   Goal = heuristic(C, Overlaps, Sections, SectionList, Cuts, ZeroCuts, Bs, Offsets),
   (  Heuristics = [Heuristic]
   -> call(Goal, Heuristic)
   ;  maplist({Goal}/[H, call(Goal, H)]>>true, Heuristics, Goals),
      first_solution(Offsets, Goals, [])
   ),
   maplist(buffer_offset, Buffers, Offsets).

challenging(File) :-
   code_type(C, upper),
   C =< 0'K,
   append([C], `.1048576.csv`, File).

benchmark :-
   findall(File, challenging(File), Files),
   maplist(csv_read_buffers, Files, BuffersList),
   maplist([File, Buffers]>>(
      call_time(minimalloc(Buffers), Time),
      get_dict(wall, Time, Wall),
      format("~s: ~3f seconds~n", [File, Wall])), Files, BuffersList).

:- begin_tests(minimalloc).

test(input12) :-
   csv_read_buffers("input.12.csv", Buffers, []),
   minimalloc(Buffers, [capacity(12), heuristics([wat])]).

:- end_tests(minimalloc).
