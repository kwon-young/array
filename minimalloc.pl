/** <minimalloc> minimalloc static algorithm implementation
 *
 * @author   Kwon-Young Choi
 * @version  1.0
 * @see      Original minimalLoc paper: https://dl.acm.org/doi/pdf/10.1145/3623278.3624752
 *
 * This module implements the MinimalLoc static memory allocation algorithm,
 * which finds non-overlapping memory positions for temporally overlapping buffers
 * while respecting capacity constraints.
 *
 * Here is an example usage:
 *
 * ==
   ?- Buffers = [
        buffer(1, 0, 3, 4, _),
        buffer(2, 3, 9, 4, _),
        buffer(3, 0, 9, 4, _),
        buffer(4, 9, 21, 4, _),
        buffer(5, 0, 21, 4, _)
    ],
    minimalloc(Buffers, [capacity(12)]).
   Buffers = [buffer(1, 0, 3, 4, 8), buffer(2, 3, 9, 4, 8), 
          buffer(3, 0, 9, 4, 4), buffer(4, 9, 21, 4, 4), 
          buffer(5, 0, 21, 4, 0)].
 * ==
 * 
 * ==
 *   Time  → 0  3  6  9  12 15 18 21
 * Offset ↓0 ┌─────────────────────┐
 *           │         5           │
 *         4 ├────────┬────────────┤
 *           │   3    │      4     │
 *         8 ├──┬─────┼────────────┘
 *           │1 │  2  │
 *        12 └──┴─────┘
 * ==
 */

:- module(minimalloc, [minimalloc/1, minimalloc/2]).

:- use_module(library(record)).
:- use_module(library(heaps)).
:- use_module(library(macros)).
:- use_module(library(csv)).
:- use_module(library(yall)).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 * records used in this implementations
 * - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -*/

%   Public buffer type representation
%
%   Fields:
%   * id     - Identifier for the buffer, not used by the implementation
%   * start  - Start time of the buffer
%   * end    - End time of the buffer
%   * size   - Size of the buffer
%   * offset - Offset value for buffer positioning
:- record buffer(id, start:integer, end:integer, size:integer, offset).

%   Internal buffer representation
%
%   Fields:
%   * offset - Current offset value for positioning, when allocated, it is wrapped in an allocated(Offset) compound
%   * index  - Current static ordering index, updated for each new partition
%   * id     - Unique identifier
%   * static - one of wat, taw or twa heuristic compound used for static ordering
%   * height - Current height of the buffer, e.g. height = offset + size
%   * size   - Size of the buffer
%   * start  - Start time
%   * end    - End time
:- record b(offset, index:integer, id:integer, static, height, size:integer, start:integer, end:integer).

%  macros to directly index field of a b compound using their argument index
%  useful for sorting on a specific argument or when using `arg/3`
#define(offset, 1).
#define(id, 3).
#define(static, 4).
#define(height, 5).

%  Heuristic compounds used for static ordering.
%  Because of the total field which changes throughout the inference, we need
%  to update these compounds for every new partitions found.
%
%  Fields:
%  * width - timespan of the buffer, e.g. width = end - start
%  * area  - Area of the buffer, e.g. area = size * width
%  * total - Current max total of all sections intersecting this buffer
%  * id    - unique identifier of the buffer, inverted since we order these compounds from largest to smallest
:- record wat(width:integer, area:integer, total:integer, id:integer).
:- record taw(total:integer, area:integer, width:integer, id:integer).
:- record twa(total:integer, width:integer, area:integer, id:integer).

%  Section as used by the minimalloc algorithm, also called a cross-section.
%  These are built from distinct end times of all buffers.
%
%  Fields:
%  id    - Section unique id
%  floor - lowest viable offset for unallocated buffers, the maximum of (the maximum height of allocated buffers) and (minimum offset of unallocated buffers (also called effective height))
%  total - sum of the sizes of unallocated buffers
%  bs    - current list of unallocated buffers crossing this section
%  end   - the end time of this section
:- record section(id, floor, total, bs, end).

#define(floor, 2).
#define(total, 3).
#define(bs, 4).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 * helper predicates for loading buffers from csv files.
 * The files comes from the original minimalloc project.
 * - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -*/

%! csv_read_buffers(+File, -Buffers:list(buffer)) is det.
%! csv_read_buffers(+File, -Buffers:list(buffer), +Options:list) is det.
%
%  Read CSV file from the original minimalloc project and convert rows into buffer terms.
%  The first row is treated as a header and excluded from the output.
%
%  Available options:
%
%  - head(+Count:int)
%    Only return the first Count rows from the CSV file
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

%!  add_offset(+BufferIn:buffer, -BufferOut:buffer) is det.
%
%   Ensures buffer term has an offset field by converting 4-argument buffer terms
%   to 5-argument buffer terms. If input already has offset, passes it through unchanged.
add_offset(buffer(Id, Start, End, Size), buffer(Id, Start, End, Size, _Offset)).
add_offset(buffer(Id, Start, End, Size, Offset), buffer(Id, Start, End, Size, Offset)).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 * minimalloc algorithm implementation
 * - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -*/

%!  minimalloc(+Buffers:list(buffer)) is semidet.
%!  minimalloc(+Buffers:list(buffer), +Options:list) is semidet.
%
%  minimalloc static allocation algorithm implementation.
%  
%  The implementation will try to find a static allocation plan so that no
%  overlapping buffers in time will be allocated in overlapping spatial interval
%  while fitting under the max allocation size (1048576 by default).
%
%  Note that the minimalloc algorithm is not complete, and only finds a unique monotonic
%  correct solution in order to restrict the search space.
%
%  `Buffers` should be a list of `buffer(id, start, end, size, offset)` compounds, where:
%
%     - `id` can be anything and is left as a convenience for the user.
%     - `start` and `end` are the start and end of the timespan of the buffer.
%     - `size` is the size of the buffer.
%     - `offset` of each compound will be unified with the offset found by the minimalloc algorithm,
%       meaning you can either leave it as a variable, or test an existing solution by passing a ground offset.
%
%  Available options:
%
%     - capacity(+C:integer)
%       maximum allocation capacity. 1048576 (or 1 GiB) by default.
%     - heuristics(+Heuristics:list(oneof([wat, taw, twa])))
%       heuristics to consider. If more than one heuristic is given,
%       the implementation will try all heuristics in parallel and return the
%       first solution found. The name of the heuristics are formed from the initials
%       of width, area and total, ordered differently, which will result in different
%       static ordering.
%
%  Heuristics are not really mentioned in the original paper but is a crucial
%  part for successfully running the challenging benchmark. The basic idea is to
%  order the buffer once per new partition by trying to allocate __big__ buffers first.
%  What constitute a __big__ buffer is ambiguous as we could order buffers by
%  width (or timespan), size or area. The choices in the original implementation is to use
%  the width or area, which is the width * size.
%  An additional `total` heuristic first allocate buffers from section with the largest
%  unnallocated buffers.
%  The original implementation used an iterative deepening round robin approach to heuristics
%  by trying each heuristic for a limited number of inferences.
%  In our case, we preferred a multiprocessing approach since the `first_solution/3` predicate
%  was made explicitly for this use-case. This has the advantage of speeding significantly the
%  time to the first solution while consuming more compute resources.
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

%! heuristic(+C:integer, !Overlaps:overlaps, !Sections:sections, !SectionList:list(section),
%!           !Cuts:cuts, +ZeroCuts:list(integer), !Bs:list(b), -Offsets:list(integer),
%!           +Heuristic:oneof([wat, taw, twa])) is semidet.
%
%  Run the minimalloc algorithm with a specific heuristic.
%  When a solution is found, the allocated offsets are extracted from Bs into Offsets.
heuristic(C, Overlaps, Sections, SectionList, Cuts, ZeroCuts, Bs, Offsets, Heuristic) :-
   partitions_inference(Heuristic, C, Overlaps, Sections, SectionList, Cuts, ZeroCuts, Bs),
   maplist([B, Offset]>>b_offset(B, allocated(Offset)), Bs, Offsets),
   debug(heuristic, "heuristic ~p found solution~n", [Heuristic]).

%! partitions_inference(+Heuristic:oneof([wat, taw, twa]), +C:integer, !Overlaps:overlaps,
%!                      !Sections:sections, !SectionList:list(section), !Cuts:cuts,
%!                      +ZeroCuts:list(integer), !Bs:list(b)) is semidet.
%
%  Helper predicate to run minimalloc algorithm on multiple partitions with cut points given by `ZeroCuts`.
partitions_inference(Heuristic, C, Overlaps, Sections, SectionList, Cuts, ZeroCuts, Bs) :-
   append(ZeroCuts, [inf], ZeroCutsInf),
   foldl(partition_inference(Heuristic, C, Overlaps, Sections, Cuts),
         ZeroCutsInf, SectionList-Bs, []-[]).

%! partition_inference(+Heuristic:oneof([wat, taw, twa]), +C:integer, !Overlaps:overlaps,
%!                     !Sections:sections, !Cuts:cuts, +ZeroCut:integer,
%!                     +State:pair(list(section), list(b)), -Right:pair(list(section), list(b))) is semidet.
%
%  Run the minimalloc algorithm on a single partition where every buffer is at the left of `ZeroCut`.
%  A partition represents a temporally independent subproblem where a set of buffers'
%  lifespans do not interact with buffers in other partitions.
%
%  This is where static ordering happen on the partition buffers, only once for each partition.
%  The static ordering depends on the Heuristic chosen in `heuristic/9`.
partition_inference(Heuristic, C, Overlaps, Sections, Cuts, ZeroCut,
                    SectionList-Bs, RightSections-RightBs) :-
   partition(left_b(ZeroCut), Bs, LeftBs, RightBs),
   partition(left_section(ZeroCut), SectionList, LeftSections, RightSections),

   length(LeftBs, N),
   maplist(update_static_of_b(N, Heuristic, Sections), LeftBs),

   % static ordering on the static compound built from the current heuristic
   sort(#static, @>=, LeftBs, SortedBs),

   % the dynamic sort in inference uses the static sort order as a tie break
   % when offsets are the same, that's why the index field is in second position
   % just after the offset field.
   foldl([B, I, I1]>>(set_index_of_b(I, B), I1 is I + 1), SortedBs, 1, _),
   once(inference(SortedBs, Heuristic, C, Overlaps, Sections, LeftSections, Cuts, 0, 0)).

%! inference(!Bs:list(b), +Heuristic:oneof([wat, taw, twa]), +C:integer, !Overlaps:overlaps,
%!           !Sections:sections, !SectionList:list(section), !Cuts:cuts,
%!           +MinOffset:integer, +MinIndex:integer) is nondet.
%
%  Depth first search of possible allocation algorithm that assigns offsets to buffers. Combines
%  the three core pruning techniques of the minimalloc algorithm:
%     1. Monotonic search: enforces strictly increasing offsets and indices
%     2. Dominance pruning: skips allocations above minimum buffer height
%     3. Section inference: checks capacity constraints in each section
%        @see section_inference/5 for more information
%
%  Additional optimisation and heuristics:
%     1. Dynamic temporal decomposition: search for new partition after each inference
inference([], _, _, _, _, _, _, _, _).
inference(Bs0, Heuristic, C, Overlaps, Sections, SectionList, Cuts, MinOffset, MinIndex) :-
   Bs0 = [_|_],
   min_height(Bs0, MinHeight),

   % dynamic ordering by smallest offset first and static index to break ties
   sort(Bs0, Sorted),
   select(B, Sorted, Bs1),

   % offset and index monotonicity
   B = b(Offset, Index, _, _, _, _, _, _),
   Offset >= MinOffset,
   (  Offset == MinOffset
   -> Index >= MinIndex
   ;  true
   ),

   % dominance check
   Offset < MinHeight,

   section_inference(C, B, Overlaps, Sections, SectionList),

   update_cuts(B, Cuts, ZeroCuts),
   (  ZeroCuts == []
   -> inference(Bs1, Heuristic, C, Overlaps, Sections, SectionList, Cuts, Offset, Index)
   ;  partitions_inference(Heuristic, C, Overlaps, Sections, SectionList, Cuts, ZeroCuts, Bs1)
   ).

%! section_inference(+C:integer, !B:b, !Overlaps:overlaps, !Sections:sections,
%!                   !SectionList:list(section)) is semidet.
%
%  Updates overlapping buffers offsets and affected sections floor and total after allocating
%  a buffer B at a specific offset. Enforces memory capacity limits of every section while
%  taking into account offset monotonicity.
section_inference(C, B, Overlaps, Sections, SectionList) :-
   B = b(Offset, _, Id, _, Height, Size, _, _),
   setarg(#offset, B, allocated(Offset)),
   arg(Id, Sections, BSections),
   arg(Id, Overlaps, BOverlaps),
   % could be done with a foldl, but hot code path, avoid meta predicate
   update_min_offsets(BOverlaps, Height, Sections, [], AffectedSections),
   update_sections_floor(BSections, B, Height, Size),
   update_affected_sections(AffectedSections),
   check_sections(SectionList, C, Offset).

%! update_min_offsets(!Bs:list(b), +Height:integer, !Sections:sections,
%!                    +AffectedSectionsIn:list(section), -AffectedSectionsOut:list(section)) is det.
%
%  Update unnallocated overlapping buffers offset (and height) with the height of the newly
%  allocated buffer Height, if Height is higher than the current Offset of the
%  unnallocated buffer.
%  The set of overlapping buffers are not updated when a buffer is allocated,
%  meaning that we have to filter out allocated buffers by checking if the offset
%  is an integer (meaning it is unnallocated).
%  When allocated, the offset is wrapped in a compound `allocated(Offset)`.
%
%  Gather affected sections in AffectedSectionsOut.
update_min_offsets([], _, _, AffectedSections, AffectedSections).
update_min_offsets([B2 | Bs], Height1, Sections, Sections1, Sections3) :-
   B2 = b(Offset2, _, Id, _, _, Size2, _, _),
   (  integer(Offset2), Offset2 < Height1
   -> NewHeight2 is Height1 + Size2,
      setarg(#offset, B2, Height1),
      setarg(#height, B2, NewHeight2),
      arg(Id, Sections, B2Sections),
      ord_union(Sections1, B2Sections, Sections2)
   ;  Sections2 = Sections1
   ),
   update_min_offsets(Bs, Height1, Sections, Sections2, Sections3).
   
%! update_sections_floor(!Sections:list(section), +B:b, +Height:integer, +Size:integer) is det.
%
%  Update section floor and total given that B has been allocated.
%  Also remove B from the set of unnallocated buffers in the section.
update_sections_floor([], _, _, _).
update_sections_floor([Section | Sections], B, Height, Size) :-
   Section = section(_, _, Total1, Bs1, _),
   Total2 is Total1 - Size,
   setarg(#floor, Section, Height),
   setarg(#total, Section, Total2),
   ord_del_element(Bs1, B, Bs2),
   setarg(#bs, Section, Bs2),
   update_sections_floor(Sections, B, Height, Size).

%! effective_height(+Bs:list(b), +MinOffsetIn:integer, -MinOffsetOut:integer) is det.
%
%  Helper predicate to compute the minimum offset of a list of unnallocated buffers,
%  also called effective height.
%
%  Incidentally this predicate is also the hottest code path in all the implementation.
%  Equivalent to:
%  ==
%  maplist(b_offset, Bs, Offsets),
%  min_list(Offsets, EffectiveHeight).
%  ==
effective_height([], Min, Min).
effective_height([B | Bs], Min1, Min3) :-
   % hottest code path, avoid extra predicate call
   B = b(Offset, _, _, _, _, _, _, _),
   % b_offset(B, Offset),
   (  Offset < Min1
   -> effective_height(Bs, Offset, Min3)
   ;  effective_height(Bs, Min1, Min3)
   ).


%! update_affected_sections(!AffectedSections:list(section)) is det.
%
%  Update the floor of sections affected by overlapping buffers changing offsets.
%  The floor of a section is update only if the effective height of unnallocated
%  buffers is higher than the current floor.
update_affected_sections([]).
update_affected_sections([Section | Sections]) :-
   % hot code path, avoid extra predicate call
   Section = section(_, Floor, _, Bs, _),
   effective_height(Bs, inf, MinOffset),
   (  Floor < MinOffset
   -> setarg(#floor, Section, MinOffset)
   ;  true
   ),
   update_affected_sections(Sections).

%! check_sections(+Sections:list(section), +C:integer, +Offset:integer) is semidet.
%
%  Check if the sum of floor and total of a section fits in the given capacity.
%  Enforce floor monotonicity by taking the maximum of the floor and the newly
%  allocated buffer offset.
check_sections([], _, _).
check_sections([Section | Sections], C, Offset) :-
   Section = section(_, Floor, Total, _, _),
   max(Offset, Floor) + Total =< C,
   check_sections(Sections, C, Offset).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 * minimalloc setup predicates
 * - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -*/

%! buffer_b(+Id:integer, +Buffer:buffer, -B:b) is det.
%
%  Convert a buffer to the internal buffer `b` representation.
%  `Id` should be a unique integer identifying this buffer starting at 1.
%  These ids will be used to index (through `arg/3`) overlapping buffers or
%  intersecting sections of the buffer.
buffer_b(Id, Buffer, B) :-
   buffer_start(Buffer, Start),
   buffer_end(Buffer, End),
   buffer_size(Buffer, Size),
   make_b([id(Id), start(Start), end(End), size(Size), offset(0), height(Size),
           index(Id)], B).

%! bs_overlaps(+Bs:list(b), -Compound:overlaps) is det.
%
%  Compute buffer overlaps and stores the results in `Overlaps`.
%  The overlapping buffers of a buffer with id `Id` can be then accessed with
%  `arg(Id, Compound, Overlaps).`.
bs_overlaps(Bs, Compound) :-
   list_to_ord_set(Bs, Set),
   maplist(b_overlaps(Set), Bs, Overlaps),
   compound_name_arguments(Compound, overlaps, Overlaps).

%! b_overlaps(+Bs:list(b), B:b, Overlaps:list(b)) is det.
%
%  Filter `Bs` so that only overlapping buffers of `B` remains in `Overlaps`.
%
%  Note that `Bs` should be an ordered set of bs, resulting in `Overlaps`
%  to also be an ordered set of bs, excluding `B`.
b_overlaps(Bs, B, Overlaps) :-
   include(overlap(B), Bs, AllOverlaps),
   ord_del_element(AllOverlaps, B, Overlaps).

%! overlap(+B1:b, +B2:b) is semidet.
%  
%  Check if `B1` and `B2` overlaps in the time dimension.
overlap(B1, B2) :-
   b_start(B1, Start),
   b_end(B1, End),
   overlap(Start, End, B2).

%! overlap(+Start1:integer, +End1:integer, +B2:b) is semidet.
%  
%  Check if the timespan `Start1`:`End1` and `B2` overlaps in the time dimension.
overlap(Start1, End1, B2) :-
   b_start(B2, Start2),
   b_end(B2, End2),
   End1 > Start2, Start1 < End2.

%! bs_cuts(+Bs:list(b), -Compound:cuts, -ZeroCuts:list(integer)) is det.
%
%  Build a reverse mapping Compound of cuts for each buffer in Bs.
%  A `cut(N:integer, V:integer)` represents a point in time `V` where `N` buffers
%  intersect, used for efficient partition tracking during memory allocation inference.
%
%  `Compound` with function `cuts/N` is used as a reversed mapping to store list of cuts
%  inside a buffer, so that they can be easily retrieved when allocating a buffer.
%  `ZeroCuts` are the list of end times which no buffers intersects even before
%  starting the first inference.
bs_cuts(Bs, Compound, ZeroCuts) :-
   maplist(b_end, Bs, Ends),
   sort(Ends, SortedEnds),
   once(append(Vs, [_], SortedEnds)),
   maplist([V, cut(0, V)]>>true, Vs, Cuts),
   length(Bs, N),
   compound_name_arity(Compound, cuts, N),
   maplist(b_cuts(Cuts, Compound), Bs),
   convlist([cut(0, V), V]>>true, Cuts, ZeroCuts).

%! b_cuts(!Cuts:list(cut), +Compound:cuts, +B:b) is det.
%
%  Associates relevant cuts with a specific buffer in the cuts compound.
%  For each cut that intersects with buffer B, increments the cut's counter
%  and stores it in B's position in Compound.
b_cuts(Cuts, Compound, B) :-
   convlist(b_cut(B), Cuts, BCuts),
   b_id(B, Id),
   arg(Id, Compound, BCuts).

%! b_cut(+B:b, !Cut:cut, -Cut:cut) is semidet.
%
%  Tests if a cut's timestamp falls within a buffer's timespan and
%  increments the cut's counter if true.
b_cut(B, Cut, Cut) :-
   Cut = cut(N, V),
   inside(V, B),
   N1 is N + 1,
   setarg(1, Cut, N1).

%! inside(+Point:integer, +B:b) is semidet.
%
%  Tests if a point in time falls strictly within a buffer's timespan.
inside(Point, B) :-
   b_start(B, L),
   b_end(B, U),
   L < Point, Point < U.

%! bs_sections(+Bs:list(b), -SectionList:list(section), -Compound:sections) is det.
%
%  Partitions buffers into sections based on their end times and overlaps.
%  Creates an ordered list of sections and a compound storing buffer-section associations.
%
%  @see bs_section/6 for individual section creation
bs_sections(Bs, SectionList, Compound) :-
   maplist(b_end, Bs, Ends),
   sort(Ends, SortedEnds),
   length(SortedEnds, N),
   numlist(1, N, Ids),
   foldl(bs_section(Bs), Ids, SectionList, SortedEnds, -inf, _),
   maplist(b_sections(SectionList), Bs, Sections),
   compound_name_arguments(Compound, sections, Sections).

%! bs_section(+Bs:list(b), +Id:integer, -Section:section, +End:integer, +Start:integer, -End:integer) is det.
%
%  Creates a single section from a list of buffers that overlap within
%  the [Start,End] interval.
%  See section record definition for individual fields documentation.
bs_section(Bs, Id, Section, End, Start, End) :-
   include(overlap(Start, End), Bs, SectionBs),
   list_to_ord_set(SectionBs, BsSet),
   maplist(b_size, SectionBs, Sizes),
   sum_list(Sizes, Total),
   make_section([id(Id), floor(0), total(Total), bs(BsSet), end(End)], Section).

b_sections(SectionList, B, Sections) :-
   include(b_section(B), SectionList, Sections).

b_section(B, Section) :-
   section_bs(Section, Bs),
   ord_memberchk(B, Bs).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 * partition helper predicates
 * - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -*/

%! left_b(+Cut:integer, +B:b) is semidet.
%
%  B is at the left of Cut.
left_b(Cut, B) :-
   b_end(B, End),
   End =< Cut.

%! left_section(+Cut:integer, +Section:section) is semidet.
%
%  Section is at the left of Cut.
left_section(Cut, Section) :-
   section_end(Section, End),
   End =< Cut.

%! update_static_of_b(+N:integer, +Heuristic:oneof([wat, taw, twa]), +Sections:sections, !B:b) is det.
%
%  update the static compound for the given Heuristic.
%  See the record definitions of the static compound for a detailed explanation of each fields.
%  A specific heuristic consists in the different ordering of each field, but all heuristics
%  uses the same fields: width, area and total.
%  The buffer original id is also used as a tie breaker.
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

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 * inference helper predicates
 * - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -*/

%! min_height(+Bs:list(b), -MinHeight:integer) is det.
%
%  Helper predicate extracting the minimum height of unnallocated buffers.
min_height(Bs, MinHeight) :-
   sort(#height, @<, Bs, [B | _]),
   b_height(B, MinHeight).

%! update_cuts(+B:b, !Cuts:cuts, -ZeroCuts:list(integer)) is det.
%
%  Update cuts inside of B by reducing the cut counter by 1.
%  Also retrieve zero cuts for new partitions.
update_cuts(B, Cuts, ZeroCuts) :-
   b_id(B, Id),
   arg(Id, Cuts, BCuts),
   foldl(update_cut, BCuts, ZeroCuts, []).

%! update_cut(!Cut:cut, +ZeroCutsIn:list(integer), +ZeroCutsOut:list(integer)) is det.
%
%  Decrement Cut counter by 1, storing the cut in ZeroCutsOut if the counter is 0.
update_cut(Cut, ZeroCuts1, ZeroCuts2) :-
   Cut = cut(N, V),
   N1 is N - 1,
   setarg(1, Cut, N1),
   (  N1 == 0
   -> ZeroCuts1 = [V | ZeroCuts2]
   ;  ZeroCuts1 = ZeroCuts2
   ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 * benchmarking
 * - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -*/

challenging_heuristic("benchmarks/A.1048576.out.csv", twa).
challenging_heuristic("benchmarks/B.1048576.out.csv", taw).
challenging_heuristic("benchmarks/C.1048576.out.csv", taw).
challenging_heuristic("benchmarks/D.1048576.out.csv", wat).
challenging_heuristic("benchmarks/E.1048576.out.csv", twa).
challenging_heuristic("benchmarks/F.1048576.out.csv", twa).
challenging_heuristic("benchmarks/G.1048576.out.csv", twa).
challenging_heuristic("benchmarks/H.1048576.out.csv", taw).
challenging_heuristic("benchmarks/I.1048576.out.csv", twa).
challenging_heuristic("benchmarks/J.1048576.out.csv", twa).
challenging_heuristic("benchmarks/K.1048576.csv", twa).

benchmarks :-
   findall(File-H, challenging_heuristic(File, H), FilesHeuristics),
   maplist(benchmark, FilesHeuristics, Times),
   sum_list(Times, Total),
   format("Total: ~3f seconds~n", [Total]).

benchmark(File-Heuristic, Wall) :-
   csv_read_buffers(File, Buffers),
   call_time(minimalloc(Buffers, [heuristics([Heuristic])]), Time),
   get_dict(wall, Time, Wall),
   format("~s: ~3f seconds~n", [File, Wall]).

:- begin_tests(minimalloc).

test(input12) :-
   csv_read_buffers("benchmarks/input.12.csv", Buffers, []),
   minimalloc(Buffers, [capacity(12), heuristics([wat])]).

:- end_tests(minimalloc).
