:- module(compile, [program/2, eval/3, kernels/3, source/2, run/4, device_options/2, allocate/8, lifetimes/2]).
:- use_module(library(clpBNR)).
:- use_module(library(dcg/high_order)).
:- use_module(core).
:- use_module(opencl).
:- use_module(buffer).
:- use_module(minimalloc).
:- use_module(reference).
:- discontiguous items_code/6.

% The pipeline, from the boxes of core to OpenCL:
%   program:  the boxes an output depends on, each after the boxes it reads;
%   fuse:     a pure name, one box, one equation, its targets its indices, is substituted
%             into its readers and its box dropped;
%   schedule: a box is a kernel of work items. An axis is parallel when no written name is
%             accessed at places that differ along it; the first parallel axes are work items,
%             tiled in strips, and the others loops. A written name whose accesses are all the
%             same and depend on the work item and the tiles alone lives in private memory.
%             But a chain of boxes over the same rows, reducing by monoids, is one kernel of
%             work-groups: a group per row, its items sharing each reduction through local
%             memory, a barrier between the boxes;
%             A box over one sequential axis whose equations are boxes with parallel work
%             is a host loop: its boxes are kernels taking the index as a parameter; a box
%             of parallel axes alone whose equations are boxes with a warp of points is a
%             sweep of one step, a group per point with the point's slices in local memory;
%             a loop nest folding one place by a monoid accumulates it in a register;
%   print:    one OpenCL C kernel per box or chain, an element typed by its name's kind, int
%             for bool and int, float for float, indices int, the integer operations of a
%             subscript or an int value as C's; the staged and vectorised kernels take float
%             elements, and load a read that is not affine one element at a time;
%   allocate: the inputs and the output each a buffer; the intermediates offsets into one
%             arena, laid out by minimalloc from their lifetimes over the kernel sequence;
%             a kernel takes each buffer as a pointer and an element offset into it;
%   run:      the extents bound by the data, in a scope undone after the run, the buffers on
%             the device, kernels in program order, the output read back.
% An extent may stay unknown through the pipeline: a kernel takes it as an int parameter, a
% decision on parallelism takes its least value, one on fit its most, and one on divisibility
% asks for it to be known; so one source, compiled once, serves every size.
% eval/3 is the reference: the boxes run in Prolog, in their order, on data(...) terms.

% program(+Out, -Boxes): the boxes Out depends on, in an order where each box comes after the
% boxes of every name it mentions, but a later box of a name it writes.
program(Out, Boxes) :-
   boxes_of(Out, Bs),
   foldl(visit([]), Bs, [], Rev),
   reverse(Rev, Boxes).

boxes_of(Name, Boxes) :-
   get_attr(Name, core, def(_, Boxes)).

visit(_, Box, Seen0, Seen), in_list(Seen0, Box) => Seen = Seen0.
visit(Stack, Box, _, _), in_list(Stack, Box) => domain_error(acyclic, Box).
visit(Stack, Box, Seen0, Seen) =>
   names(Box, Names),
   foldl(before(Box), Names, [], Deps),
   foldl(visit([Box | Stack]), Deps, Seen0, Seen1),
   Seen = [Box | Seen1].

% before(+Box, +Name, +Deps0, -Deps): the boxes of Name that must run before Box.
before(Box, Name, Deps0, Deps) :-
   boxes_of(Name, Bs),
   (  append(Earlier, [B | _], Bs), same_term(B, Box)
   -> append(Deps0, Earlier, Deps)
   ;  append(Deps0, Bs, Deps)
   ).

% in_list(+List, +X): X is an element of List, the same term.
in_list(List, X) :-
   member(Y, List),
   same_term(X, Y),
   !.

% names(+Term, -Names): the names Term mentions, the attributed variables among its variables.
names(Term, Names) :-
   term_variables(Term, Vars),
   include(is_name, Vars, Names).

% label_program(+Out, +Boxes): the kinds of the names of Boxes and Out resolved, see label_kinds/1.
label_program(Out, Boxes) :-
   names(Boxes, Names0),
   list_to_set([Out | Names0], Names),
   label_kinds(Names).

% ctype(+N, -T): the C type of the elements of N: int for a bool or an int, float for a float,
% and float while the kind is unresolved, a name the compiler made.
ctype(N, T) :-
   core:name_kind(N, K),
   (  integer(K), K < 2
   -> T = int
   ;  T = float
   ).

% kind_of(+E, -K): the kind of the value E, 0, 1 or 2, once the names are labelled: the rules of
% core:value_kind/3 on numbers.
kind_of(V, K), var(V), is_name(V) => core:name_kind(V, K0), ( integer(K0) -> K = K0 ; K = 2 ).
kind_of(V, K), var(V) => K = 1.
kind_of(N, K), number(N) => core:number_kind(N, K).
kind_of(R, K), core:place(R, N, _) => kind_of(N, K).
kind_of(where(_, T, E), K) => kind_of(T, KT), kind_of(E, KE), K is max(KT, KE).
kind_of(E, K), E =.. [Op, _, _], memberchk(Op, [<, =<, =:=]) => K = 0.
kind_of(E, K), E =.. [Op | _], memberchk(Op, [/, sqrt, exp, log]) => K = 2.
kind_of(bits(_), K) => K = 1.
kind_of(E, K), compound(E) => E =.. [_ | As], maplist(kind_of, As, Ks), max_list([1 | Ks], K).

is_name(V) :-
   get_attr(V, core, _).

% Fusion
% ======

% fuse(+Out, +Boxes0, -Boxes): Boxes0 with each pure name but Out substituted into the boxes
% that read it. A name is pure when one box writes it, in one equation whose targets are the
% box's indices, and the names its value reads are not written again afterwards; a
% permutation stays, the scatters through it depend on reading it.
fuse(Out, Boxes0, Boxes) :-
   fuse(Out, Boxes0, [], Boxes).

fuse(_, [], Rev, Boxes) =>
   reverse(Rev, Boxes).
fuse(Out, [Box | Later0], Rev, Boxes), pure(Out, Box, Later0, N, Is, V) =>
   maplist(inline(N, Is, V), Later0, Later),
   fuse(Out, Later, Rev, Boxes).
fuse(Out, [Box | Later], Rev, Boxes) =>
   fuse(Out, Later, [Box | Rev], Boxes).

pure(Out, over(Axes, [P := V]), Later, N, Is, V) :-
   core:place(P, N, Ts),
   N \== Out,
   \+ get_attr(N, perm, _),                        % a permutation is read as such, see covers/3
   boxes_of(N, [_]),
   maplist(arg(1), Axes, Is),
   permutation_eq(Is, Ts),
   names(V, Read),
   \+ ( member(M, Read), member(B, Later), core:writes(B, Ws), in_list(Ws, M) ),
   \+ ( member(B, Later), reused(B, N) ).

% reused(+Box, +N): Box reads N at a subscript that leaves one of its axes out, so each
% element is read at several points; inlined, its value would be computed at each of them.
reused(over(Axes, Eqs), N) :-
   maplist(arg(1), Axes, Is),
   accesses(over(Axes, Eqs), N, Ss),
   member(S, Ss), member(I, Is), \+ mentions(S, I), !.

permutation_eq(Is, Ts) :-
   sort(Is, S),
   sort(Ts, S),
   same_length(Is, Ts).

% inline(+N, +Is, +V, +T0, -T): T0 with every read of N at Es replaced by V at Es.
inline(N, _, V, T0, T), var(T0), T0 == N => T = V.
inline(_, _, _, T0, T), var(T0) => T = T0.
inline(N, Is, V, [](Es0, A), T), A == N =>
   maplist(inline(N, Is, V), Es0, Es),
   pairs_keys_values(Pairs, Is, Es),
   subst(Pairs, V, T).
inline(N, Is, V, T0, T), compound(T0) =>
   T0 =.. [F | As0],
   maplist(inline(N, Is, V), As0, As),
   T =.. [F | As].
inline(_, _, _, T0, T) => T = T0.

% subst(+Pairs, +T0, -T): T0 with each variable of Pairs replaced by its value.
subst(Pairs, T0, T), var(T0), member(K-X, Pairs), K == T0 => T = X.
subst(Pairs, T0, T), compound(T0) =>
   T0 =.. [F | As0],
   maplist(subst(Pairs), As0, As),
   T =.. [F | As].
subst(_, T0, T) => T = T0.

% Scheduling
% ==========

% kernels(+Out, +Options, -Kernels): the kernels computing Out, after fusion, from the options
% tile(T), the strip of a work item, local(L), the items of a work-group, a power of two, and
% items(Min), the parallelism under which a reduction goes to a work-group; lanes(U), the
% items a work-group occupies at the least, the warp: a row narrower than U runs in one work
% item; epilogue(false) keeps a reduction's initialisation and epilogue as kernels of their
% own.
kernels(Out, Options, Kernels) :-
   option(tile(Tile), Options, 4),
   option(local(L), Options, 64),
   option(items(Min), Options, 64),
   option(group(G), Options, 8),
   option(stage(TK), Options, 8),
   option(vector(W), Options, 4),
   option(major(Major), Options, k_first),
   option(threads(Threads), Options, 0),
   option(panel(KC, MC), Options, panel(256, 64)),
   option(lds(LDS), Options, 16384),
   option(sweep(SW), Options, L),
   option(epilogue(Epi), Options, true),
   option(lanes(U), Options, 32),
   must_be(positive_integer, L),
   L /\ (L-1) =:= 0,
   program(Out, Boxes0),
   label_program(Out, Boxes0),
   fuse(Out, Boxes0, Boxes1),
   splits(Boxes1, L, Min, Boxes),
   chains(Boxes, Out, Boxes, opts(Tile, G, TK, W, Major, Threads, KC, MC, Min, L, Epi, LDS, U), L-LDS-SW, Min, [], Plan),
   number_plan(Plan, 0, _, Kernels).

% number_plan(+Plan0, +I0, -I, -Plan): each kernel of the plan, a tree of kernels and host
% loops loop(T, E, Plan), gets its id, its position in the source.
number_plan([], I, I1, Plan) => I1 = I, Plan = [].
number_plan([loop(T, E, Inner0) | Ps0], I0, I, Plan) =>
   number_plan(Inner0, I0, I1, Inner), Plan = [loop(T, E, Inner) | Ps], number_plan(Ps0, I1, I, Ps).
number_plan([K0 | Ps0], I0, I, Plan) =>
   kernel_extents(K0, Extents),
   K = K0.put(_{id: I0, extents: Extents}), I1 is I0+1, Plan = [K | Ps], number_plan(Ps0, I1, I, Ps).

% flat_plan(+Plan, -Kernels): the kernels of the plan in source order.
flat_plan(Plan, Kernels) :-
   foldl(flat_kernel, Plan, [], Rev),
   reverse(Rev, Kernels).

flat_kernel(loop(_, _, Inner), Acc0, Acc) => foldl(flat_kernel, Inner, Acc0, Acc).
flat_kernel(K, Acc0, Acc) => Acc = [K | Acc0].

% splits(+Boxes0, +L, +Min, -Boxes): a reduction into few places over a long axis is split: a
% partial reduction over each of C chunks of the axis, into a new name with a chunk axis, and
% a reduction of the partials. The chunks keep fewer than Min places, so both go to groups.
splits(Boxes0, L, Min, Boxes) :-
   foldl(split(L, Min), Boxes0, [], Rev),
   reverse(Rev, Boxes).

split(L, Min, Box, Acc, Acc1), splittable(Box, L, Min, [Init, Partial, Combine]) =>
   reorder(Acc, Init, Partial, Combine, Acc1).
split(_, _, Box, Acc, Acc1) => Acc1 = [Box | Acc].

% reorder(+Acc, +Init, +Partial, +Combine, -Acc1): the partials go before the box that
% initialises the target, so that each stays in a chain with its own initialisation.
reorder([Prev | Acc], Init, Partial, Combine, Acc1), init_of(Prev, Combine) =>
   Acc1 = [Combine, Prev, Partial, Init | Acc].
reorder(Acc, Init, Partial, Combine, Acc1) =>
   Acc1 = [Combine, Partial, Init | Acc].

init_of(over(_, [P := V]), over(_, [P1 := _])) :-
   number(V),
   core:place(P, G, _),
   core:place(P1, G1, _),
   G == G1.

splittable(over(Axes, [P := V]), L, Min, [Init, Partial, Combine]) :-
   Box = over(Axes, [P := V]),
   include(parallel(Box, []), Axes, Rows),
   maplist(arg(1), Rows, RowIs),
   exclude(axis_in(RowIs), Axes, [K:D]),
   reduction(RowIs, P := V, red(G, Ts, Op, E)),
   maplist(arg(2), Rows, Es),
   size(Es, NRows),
   NRows < Min,
   ground(D),
   extent(D, N),
   chunks(N, NRows, L, Min, C),
   C >= 2,
   Chunk is N // C,
   shape(G, Shape),
   shape(Gp, [C | Shape]),
   core:kind(G, Kind), core:kind(Gp, Kind),
   ctype(G, T), identity(Op, T, Identity),
   subst([K-(Kc*Chunk + Ki)], E, E1),
   Subs = [Kc | Ts],
   Partials = [](Subs, Gp),
   Step =.. [Op, Partials, E1],
   Fold =.. [Op, P, Partials],
   Init = over([Kc:C | Rows], [Partials := Identity]),
   append(Rows, [Ki:Chunk], Axes1),
   Partial = over([Kc:C | Axes1], [Partials := Step]),
   append(Rows, [Kc:C], Axes2),
   Combine = over(Axes2, [P := Fold]).

% chunks(+N, +NRows, +L, +Min, -C): the most chunks dividing N that keep NRows*C under Min and
% give each chunk L elements at least.
chunks(N, NRows, L, Min, C) :-
   Most is min((Min - 1) // max(NRows, 1), N // L),
   aggregate_all(max(D), ( between(1, Most, D), N mod D =:= 0 ), C).

% chains(+Boxes, +Out, +All, +Opts, +L, +Min, +Free, -Plan): a box over one sequential axis
% whose equations are boxes with at least Min parallel points is a host loop over its boxes,
% the index free in them; a chain worth a work-group kernel is one; a reduction with its
% initialisation and elementwise epilogue is one kernel of work items; any other box is a
% kernel of work items. Free holds the indices of the host loops around.
chains([], _, _, _, _, _, _, Plan) =>
   Plan = [].
chains([B | Bs], Out, All, Opts, L, Min, Free, Plan), sweep(B, Opts, L, Min, Free, K) =>
   Plan = [K | Ps],
   chains(Bs, Out, All, Opts, L, Min, Free, Ps).
chains([B | Bs], Out, All, Opts, L, Min, Free, Plan), host_loop(Out, All, B, Min, T, E, Inner) =>
   chains(Inner, Out, All, Opts, L, Min, [T | Free], Ks0),
   Plan = [loop(T, E, Ks0) | Ps],
   chains(Bs, Out, All, Opts, L, Min, Free, Ps).
chains([B | Bs], Out, All, Opts, L, Min, Free, Plan), chain([B | Bs], Rows, Phases, Rest), worth(Rows, Phases, Min, Free),
      L = Items-_-_, group_local(Opts, Phases, Items, Rows, Min, Free, Local) =>
   names(Phases, Names),
   Plan = [kernel{kind: groups, rows: Rows, phases: Phases, local: Local, names: Names, free: Free, shared: []} | Ps],
   chains(Rest, Out, All, Opts, L, Min, Free, Ps).

% group_local(+Opts, +Phases, +Items, +Rows, +Min, +Free, -Local): the work-group of a chain
% holds Items work items at most, and as many as leave 8 elements of its longest reduction
% to each, a power of two, and the lanes a group occupies at the least. Fails, so that the
% chain goes to kernels of work items, when the reduction cannot fill those lanes while the
% rows alone fill the device: a group would idle its lanes and pay its barriers for nothing.
% With fewer rows the lanes are the only parallelism left, and inside a host loop the
% launches saved are worth it.
group_local(Opts, Phases, Items, Rows, Min, Free, Local) :-
   aggregate_all(max(N), ( member(reduce(_:D, _), Phases), extent(D, N) ), Row),
   !,
   arg(13, Opts, Lanes),
   Share is max(1, Row // 8), Fit is 1 << msb(Share),
   maplist(arg(2), Rows, Es), size(Es, NRows),
   ( Fit >= Lanes -> true ; Free = [_ | _] -> true ; NRows < Min ),
   Local is max(Lanes, min(Items, Fit)).
group_local(_, _, Items, _, _, _, Items).
chains([B | Bs], Out, All, Opts, L, Min, Free, Plan), arg(11, Opts, true),
      epilogue(Out, All, [B | Bs], Before, Init0, Red, Post0, Temps, Rest),
      schedule(Out, All, Opts, Red, K0), get_dict(atomics, K0, []),  % not an atomic reduction
      rows_are_items(K0) =>
   chains(Before, Out, All, Opts, L, Min, Free, PsB),
   restrip(K0, Init0, Init), restrip(K0, Post0, Post),
   get_dict(names, K0, Names0), names(Init-Post, Names1), append(Names0, Names1, Names2), list_to_set(Names2, Names3),
   exclude(in_list(Temps), Names3, Names),
   K = K0.put(_{pre: Init, post: Post, temps: Temps, free: Free, names: Names}),
   append(PsB, [K | Ps], Plan),
   chains(Rest, Out, All, Opts, L, Min, Free, Ps).
chains([B | Bs], Out, All, Opts, L, Min, Free, Plan) =>
   schedule(Out, All, Opts, B, K0),
   K = K0.put(free, Free),
   Plan = [K | Ps],
   chains(Bs, Out, All, Opts, L, Min, Free, Ps).

% rows_are_items(+K): every row of the reduction K is a work item or a tile, so that its one
% loop is the reduction's axis, the initialisation runs before it and the epilogue after it;
% a sequential row would have to carry them inside its loop.
rows_are_items(K) :-
   kernel{seq: Seq, tiles: TilePairs} :< K,
   pairs_values(TilePairs, TileIs),
   exclude(axis_in(TileIs), Seq, [_]).

% epilogue(+Out, +All, +Boxes, -Before, -Init, -Red, -Post, -Temps, -Rest): the first boxes are a
% chain over one point set: a box initialising a name C, a reduction into C over one more axis,
% and elementwise boxes reading C at the point and writing others: one kernel, C accumulated
% in registers, the initialisation before its loop and the elementwise work after it, C a
% temporary when nothing later reads it. The boxes' indices are renamed to the reduction's.
% Boxes between the initialisation and the reduction that neither mention C nor write what
% the initialisation reads come Before the kernel.
epilogue(Out, All, [InitBox | Bs0], Before, Init, Red, Post, Temps, Rest) :-
   InitBox = over(AxesI, [PI := VI]),
   core:place(PI, C, TsI),
   names(VI, NsI), \+ in_list(NsI, C),
   before(C, NsI, Bs0, Before, [Red | Bs]),
   Red = over(AxesR, [PR := VR]),
   core:place(PR, C1, TsR), C1 == C,
   VR =.. [Op, R, _], monoid(Op, _), core:place(R, C2, TsR1), C2 == C, TsR1 == TsR,
   maplist(arg(1), AxesI, IsI), maplist(arg(1), AxesR, IsR),
   term_variables(TsR, VsR), forall(member(V, VsR), in_list(IsR, V)),
   length(IsR, NR), length(VsR, NV), NR =:= NV + 1,
   renaming(TsI, IsI, TsR, PairsI), subst(PairsI, PI := VI, InitEq),
   posts(C, TsR, Bs, PostEqs, Used, Rest),
   Init = [InitEq], Post = PostEqs,
   ( live(C, Out, All, [InitBox, Red | Used]) -> Temps = [] ; Temps = [C] ).

% before(+C, +Read, +Boxes, -Before, -Rest): the longest prefix of boxes that neither mention
% C nor write a name of Read.
before(C, Read, [B | Bs], Before, Rest) :-
   names(B, Ns), \+ in_list(Ns, C),
   core:writes(B, Ws), \+ ( member(W, Ws), in_list(Read, W) ),
   !,
   Before = [B | Before1], before(C, Read, Bs, Before1, Rest).
before(_, _, Bs, [], Bs).

% restrip(+Kernel, +Eqs0, -Eqs): Eqs0 with each strip of the kernel's box applied: an index I
% split into I*T + Ii.
restrip(K, Eqs0, Eqs) :-
   kernel{tiles: Pairs, box: over(Axes, _)} :< K,
   foldl(strip_pair(Axes), Pairs, [], Subst),
   subst(Subst, Eqs0, Eqs).

strip_pair(Axes, I-Ii, S0, [I-(I*T + Ii) | S0]) :-
   core:extent(Axes, Ii, E), extent(E, T).

% posts(+C, +Ts, +Boxes, -Eqs, -Used, -Rest): the boxes reading C at Ts over the same axes,
% renamed to Ts, until one does not: their equations, and the boxes themselves.
posts(C, Ts, [B | Bs], Eqs, Used, Rest) :-
   B = over(Axes, Eqs0),
   maplist(arg(1), Axes, Is), length(Is, N), length(Ts, N),
   forall(member(E, Eqs0), post_eq(C, Is, E)),
   accesses(over(Axes, Eqs0), C, [S | Ss]), forall(member(S1, Ss), S1 == S),
   renaming(S, Is, Ts, Pairs),
   !,
   subst(Pairs, Eqs0, Eqs1),
   posts(C, Ts, Bs, Eqs2, Used1, Rest),
   append(Eqs1, Eqs2, Eqs), Used = [B | Used1].
posts(_, _, Bs, [], [], Bs).

% post_eq(+C, +Is, +Eq): Eq writes a name but C, at a place over all the indices: elementwise.
post_eq(C, Is, P := _) :-
   core:place(P, N, Ts), N \== C,
   term_variables(Ts, Vs), forall(member(I, Is), in_list(Vs, I)).

% renaming(+TsA, +IsA, +TsB, -Pairs): the subscripts TsA, over the indices IsA, are TsB up to
% a renaming of IsA onto the indices of TsB, one to one: Pairs maps each index of IsA.
renaming(TsA, IsA, TsB, Pairs) :-
   match(TsA, TsB, IsA, [], Pairs),
   pairs_keys(Pairs, Keys), permutation_eq(Keys, IsA),
   pairs_values(Pairs, Vals), term_variables(TsB, VsB), permutation_eq(Vals, VsB).

match(A, B, IsA, P0, P), var(A) =>
   in_list(IsA, A), var(B),
   (  member(A1-B1, P0), A1 == A
   -> B1 == B, P = P0
   ;  \+ ( member(_-B2, P0), B2 == B ), P = [A-B | P0]
   ).
match(A, B, IsA, P0, P), compound(A) =>
   compound(B), A =.. [F | As], B =.. [F | Bs], length(As, N), length(Bs, N),
   foldl(match_arg(IsA), As, Bs, P0, P).
match(A, B, _, P0, P) =>
   A == B, P = P0.

match_arg(IsA, X, Y, P0, P) :- match(X, Y, IsA, P0, P).

% live(+C, +Out, +All, +Used): C is the output, or a box but the Used ones mentions it.
live(C, Out, _, _) :- C == Out, !.
live(C, _, All, Used) :- member(B, All), \+ in_list(Used, B), names(B, Ns), in_list(Ns, C), !.

% sweep(+Box, +Opts, +L-LDS, +Min, +Free, -Kernel): Box has parallel axes, its rows, then one
% sequential axis, and its equations are boxes, each a phase over its own axes: one work-group
% kernel per row point, the sequential axis a loop inside it with a fence between the phases.
% A box of parallel axes alone, its phases a warp of points at least, is a sweep of one step:
% a group per row point, its phases sharing the row's slices in local memory.
% One launch for the whole sweep, which is what a small factorisation, or a batch of them,
% wants: so when the rows are a compute unit's worth of groups, or a step's parallel points
% are a few passes of a group, or the sweep is a step of a host loop, where launches are
% the cost. A name the sweep writes whose slice of a row point fits half
% the local memory lives there for the whole sweep, copied in before and out after.
% When a step's points cannot fill the lanes a group occupies while the rows alone fill the
% device, each row point is one work item instead, its phases plain loops: no barrier, no
% idle lane.
sweep(over(Axes, Eqs), Opts, L-LDS-SW, Min, Free, Kernel) :-
   Eqs = [_ | _],
   forall(member(Q, Eqs), is_box(Q)),
   Box = over(Axes, Eqs),
   aggregate_all(max(P), ( member(over(As, _), Eqs), include(parallel(over(As, []), []), As, Par),
                           maplist(arg(2), Par, PEs), size(PEs, P) ), Points),
   arg(13, Opts, Lanes),
   (  append(Rows, [T:E], Axes), \+ parallel(Box, [], T:E)
   -> true
   ;  Points >= Lanes, Rows = Axes, E = 1
   ),
   forall(member(R, Rows), parallel(Box, [], R)),
   maplist(sweep_phase, Eqs, Phases),
   maplist(arg(2), Rows, REs), size(REs, NRows),
   ( Points < Lanes, NRows >= Min -> Item = true ; Item = false ),
   ( Item == true ; Free = [_ | _] ; NRows >= Min // 8 ; Points =< L*Min ), !,
   names(Eqs, Names),
   (  Item == true
   -> Kernel = kernel{kind: groups, rows: Rows, phases: [loop(T, E, Phases)], local: 1, item: true, names: Names,
                      free: Free, shared: []}
   ;  core:writes(Box, Written),
      maplist(arg(1), Rows, RowIs),
      length(RowIs, Drop),
      Budget is LDS // 8,
      convlist(shared_name(Box, RowIs, Drop, Budget), Written, Shared),
      Kernel = kernel{kind: groups, rows: Rows, phases: [loop(T, E, Phases)], local: SW, names: Names, free: Free,
                      shared: Shared}
   ).

% shared_name(+Box, +RowIs, +Drop, +Budget, +N, -N-Drop-Size): every access of N starts with
% the row indices, and its slice of Size floats fits Budget.
shared_name(Box, RowIs, Drop, Budget, N, N-Drop-Size) :-
   shape(N, Shape),
   length(Prefix, Drop), append(Prefix, Rest, Shape),
   size_max(Rest, Size), Size =< Budget,
   accesses(Box, N, Ss),
   forall(member(S, Ss), ( length(P, Drop), append(P, _, S), maplist([X, Y]>>(X == Y), P, RowIs) )).

sweep_phase(Box, Phase) :-
   phase([], Box, Phase).

% host_loop(+Out, +All, +Box, +Min, -T, -E, -Inner): Box runs its axis T in order, given the
% names local to it, which each step has for itself, and its equations are boxes, one of which
% has Min parallel points at least: worth a launch per step. A box whose axis is parallel but
% for a local accumulator is a kernel of work items with the accumulator private, see
% schedule/5, not a launch per point.
host_loop(Out, All, over([T:E], Inner), Min, T, E, Inner) :-
   Inner = [_ | _],
   forall(member(Q, Inner), is_box(Q)),
   locals(Out, All, over([T:E], Inner), Locals),
   \+ parallel(over([T:E], Inner), Locals, T:E),
   member(over(Axes, _), Inner),
   include(parallel(over(Axes, []), []), Axes, Par),
   maplist(arg(2), Par, Es), size(Es, N), N >= Min, !.

% worth(+Rows, +Phases, +Min): a chain reducing twice fuses its passes over the rows; one
% reducing once is worth a work-group when the rows alone would leave the device idle.
% Inside a host loop, two phases or more save a launch per step, which is worth a group
% while the rows are few; a group per row of many rows is a launch of too many groups.
worth(Rows, Phases, Min, [_ | _]) :-
   Phases = [_, _ | _],
   maplist(arg(2), Rows, Es), size(Es, N), N < Min, !.
worth(Rows, Phases, Min, _) :-
   aggregate_all(count, member(reduce(_, _), Phases), Reductions),
   maplist(arg(2), Rows, Es),
   size(Es, N),
   grouped(Reductions, N, Min).

grouped(Reductions, _, _), Reductions >= 2 => true.
grouped(Reductions, N, Min), Reductions >= 1, N < Min => true.
grouped(_, _, _) => fail.

% Chains
% ======

% chain(+Boxes, -Rows, -Phases, -Rest): the longest prefix of Boxes that is one chain. Its rows
% are the parallel axes of the first box; each later box has its parallel axes renamed to the
% rows through the names they share. Each box is a phase over the rest of its axes: serial,
% a reduction by monoids, or spread over one more parallel axis. A box reads what the chain
% wrote at its own row only: a group sees the writes of its row, not of the others.
chain([B | Bs], Rows, [P | Ps], Rest) :-
   B = over(Axes, _),
   include(parallel(B, []), Axes, Rows),
   phase(Rows, B, P),
   extend(Rows, [B], Bs, Ps, Rest).

extend(Rows, Prev, [B0 | Bs], Phases, Rest), align(Rows, Prev, B0, B), own_row(Rows, Prev, B), phase(Rows, B, P) =>
   Phases = [P | Ps],
   extend(Rows, [B | Prev], Bs, Ps, Rest).
extend(_, _, Bs, Phases, Rest) =>
   Phases = [],
   Rest = Bs.

% own_row(+Rows, +Prev, +Box): every access in Box of a name Prev writes has, where an access
% of Prev has a row index, that same index.
own_row(Rows, Prev, Box) :-
   maplist(arg(1), Rows, RowIs),
   core:writes(over([], Prev), Written),
   forall(( member(N, Written), accesses(Box, N, Ss), member(S, Ss),
            accesses(Prev, N, Ps), member(P, Ps), nth0(K, P, R), var(R), in_list(RowIs, R) ),
          ( nth0(K, S, R1), R1 == R )).

% A phase may hold boxes: loops of the item, see statement//2.
phase(Rows, over(Axes, Eqs), Phase) :-
   maplist(arg(1), Rows, RowIs),
   exclude(axis_in(RowIs), Axes, Rest),
   phase(Rest, RowIs, over(Axes, Eqs), Eqs, Phase).

phase([], _, _, Eqs, Phase) => Phase = serial(Eqs).
phase([K:D], RowIs, _, Eqs, Phase), maplist(reduction(RowIs), Eqs, Reds) => Phase = reduce(K:D, Reds).
phase(Axes, _, Box, Eqs, Phase), forall(member(A, Axes), parallel(Box, [], A)) =>
   length(Axes, N), length(Ones, N), maplist(=(1), Ones),
   ranges(Box, Axes, Ones, none, Ranges),
   Phase = spread(Axes, Ranges, Eqs).
phase(_, _, _, _, _) => fail.

% reduction(+RowIs, +Eq, -Red): Eq is G[Ts] := Op(G[Ts], E), Op a monoid, Ts over the rows
% alone, E not reading G: red(G, Ts, Op, E).
reduction(RowIs, P := V, red(G, Ts, Op, E)) :-
   core:place(P, G, Ts),
   V =.. [Op, R, E],
   monoid(Op, _),
   core:place(R, G1, Ts1),
   G1 == G,
   Ts1 == Ts,
   term_variables(Ts, Vs),
   forall(member(X, Vs), in_list(RowIs, X)),
   names(E, Ns),
   \+ in_list(Ns, G).

% monoid(?Op, ?Identity): the identity of a monoid, as a number.
monoid(+, 0).
monoid(*, 1).
monoid(max, NegInf) :- NegInf is -inf.
monoid(min, Inf) :- Inf is inf.

% identity(+Op, +T, -Identity): the identity in the C type T: an int has no infinity, its
% extremes stand in.
identity(max, int, Identity) => Identity = -2147483648.
identity(min, int, Identity) => Identity = 2147483647.
identity(Op, _, Identity) => monoid(Op, Identity).

% align(+Rows, +Prev, +Box0, -Box): Box is Box0 with its parallel axes renamed to the rows. An
% axis that shares a subscript position of a name with a row of Prev is that row; the rows
% left take the axes left, in order, as spreading independent iterations over the groups is
% always sound. Every row gets an axis of its extent, and at most one axis stays, to spread.
align(Rows, Prev, Box0, Box) :-
   Box0 = over(Axes0, _),
   include(parallel(Box0, []), Axes0, Par0),
   maplist(arg(1), Par0, ParIs),
   maplist(arg(1), Rows, RowIs),
   partners(ParIs, RowIs, Prev, Box0, Found),
   pairs_keys(Found, Ds),
   pairs_values(Found, Rs),
   distinct(Ds),
   distinct(Rs),
   exclude(in_list(Ds), ParIs, FreeDs),
   exclude(in_list(Rs), RowIs, FreeRs),
   length(FreeRs, NFree),
   length(Taken, NFree),
   append(Taken, Left, FreeDs),
   length(Left, NLeft),
   NLeft =< 1,
   pairs_keys_values(Guessed, Taken, FreeRs),
   append(Found, Guessed, Pairs),
   forall(member(D-R, Pairs), same_extent(D, Par0, R, Rows)),
   subst(Pairs, Box0, Box).

distinct(Vars) :-
   sort(Vars, Sorted),
   same_length(Vars, Sorted).

same_extent(D, Par, R, Rows) :-
   core:extent(Par, D, Ed),
   core:extent(Rows, R, Er),
   (  ground(Ed-Er)
   -> extent(Ed, N), extent(Er, N)
   ;  Ed == Er
   ).

% partners(+ParIs, +RowIs, +Prev, +Box0, -Pairs): D-R for each parallel axis D of Box0 found at
% the subscript position where Prev has the row R, in an access of the same name. The pairs
% are found as positions in Vars, as findall/3 would copy the variables.
partners(ParIs, RowIs, Prev, Box0, Pairs) :-
   term_variables(Prev-Box0, Vars),
   findall(Dn-Rn, partner(Vars, ParIs, RowIs, Prev, Box0, Dn, Rn), Ns0),
   sort(Ns0, Ns),
   maplist(pair_vars(Vars), Ns, Pairs).

partner(Vars, ParIs, RowIs, Prev, Box0, Dn, Rn) :-
   names(Box0, Ns),
   member(N, Ns),
   accesses(Box0, N, Sn),
   member(S, Sn),
   accesses(Prev, N, Sc),
   member(S1, Sc),
   nth0(P, S, D), var(D), in_list(ParIs, D),
   nth0(P, S1, R), var(R), in_list(RowIs, R),
   index_of(Vars, D, Dn),
   index_of(Vars, R, Rn).

index_of(Vars, V, N) :-
   nth0(N, Vars, V1),
   V1 == V,
   !.

pair_vars(Vars, Dn-Rn, D-R) :-
   nth0(Dn, Vars, D),
   nth0(Rn, Vars, R).

% schedule(+Out, +Boxes, +Opts, +Box, -Kernel): Kernel is the schedule of Box:
%   par    the axes that are work items, tiled in strips of Tile where Tile divides them,
%   seq    the loops of a work item, the tile axes last,
%   priv   Name-Axes: a written name private to a work item, over the tile axes it depends on,
%   local  the names written in inner boxes only and read nowhere else: private, untouched,
%   names  every other name, a buffer of the kernel,
%   stage  none, or the work-groups of G*G items and the reads staged in local memory, the
%          tile of the first strip laid out K first or K last as Major says, or, with threads,
%          the packed panels of a thread per core, see staging/14,
%   vector the width of the vector the last tile loop may become.
schedule(Out, Boxes, opts(Tile, G, TK, W, Major, Threads, KC, MC, Min, L, _, LDS, _), Box0, Kernel) :-
   locals(Out, Boxes, Box0, Locals),
   Box0 = over(Axes0, _),
   include(parallel(Box0, Locals), Axes0, Strict),
   parallel_axes(Box0, Locals, Axes0, Strict, Min*L, L, Par0),
   length(Par0, NPar),
   Keep is min(NPar, 3),
   length(Par1, Keep),
   append(Par1, _, Par0),
   maplist(arg(1), Par1, ParIs),
   Box0 = over(_, Eqs0),
   ( member(Q, Eqs0), is_box(Q) -> Tile1 = 1 ; Tile1 = Tile ),
   tiles_of(Tile1, Par1, Widths),
   pairs_keys_values(Strips, Widths, Par1),
   foldl(strip, Strips, Box0-[], Box-TilePairs0),
   reverse(TilePairs0, TilePairs),
   pairs_values(TilePairs, TileIs),
   Box = over(Axes, _),
   include(axis_in(ParIs), Axes, Par),
   include(axis_in(TileIs), Axes, Tiles),
   exclude(axis_in(ParIs), Axes, Seq0),
   exclude(axis_in(TileIs), Seq0, Seq1),
   append(Seq1, Tiles, Seq),
   core:writes(Box, Written),
   exclude(in_list(Locals), Written, Globals),
   atomics(Box, Par, Locals, Atomics),
   pairs_keys(Atomics, AtomicNames),
   exclude(in_list(AtomicNames), Globals, Plain),
   convlist(private(Box, ParIs, TilePairs), Plain, Priv),
   names(Box, All),
   exclude(in_list(Locals), All, Names),
   staging(Box, Par, Seq1, TilePairs, Written, Priv, Locals, G, TK, Major, Threads, KC, MC, LDS, Stage),
   ranges(Box0, Par1, Widths, Stage, Ranges),
   vector_width(W, All, W1),
   Kernel = kernel{kind: items, box: Box, par: Par, seq: Seq, priv: Priv, local: Locals, names: Names, tiles: TilePairs,
                   stage: Stage, vector: W1, ranges: Ranges, atomics: Atomics, pre: [], post: [], temps: []}.

% vector_width(+W, +Names, -W1): the vector width of a kernel over Names: W when every name is
% a float, else 1: the vector loads, stores and casts are float ones.
vector_width(W, Names, W1) :-
   (  forall(member(N, Names), ctype(N, float))
   -> W1 = W
   ;  W1 = 1
   ).

% ranges(+Box, +Par, +Widths, +Stage, -Ranges): when every equation of Box writes its place
% back unchanged outside a guard, the guard bounds the parallel axes: I-range(Lo, Count) in
% strips of its width, the bounds terms in the indices of the host loops around, evaluated at
% each launch. A staged kernel takes them in whole work-groups of strips; a packed one none.
ranges(Box, Par, Widths, Stage, Ranges), group_multiple(Stage, Mult), guarded(Box, Conds) =>
   maplist(arg(1), Par, Is),
   foldl(direct_bound(Conds, Is), Par, [], Bounds0),
   foldl(between_axes(Conds), Par, Bounds0, Bounds1),
   foldl(between_axes(Conds), Par, Bounds1, Bounds),
   maplist([W, W-Mult]>>true, Widths, WMs),
   foldl(strip_range(Bounds), Par, WMs, [], Ranges).
ranges(_, _, _, _, Ranges) =>
   Ranges = [].

group_multiple(none, Mult) => Mult = 1.
group_multiple(stage(G, _, _), Mult) => Mult = G.
group_multiple(_, _) => fail.

% guarded(+Box, -Conds): the conjunction of guards every equation of Box is under, given that
% each writes its own value back where the guard fails: P := where(C, V, P).
guarded(over(_, Eqs), Conds) :-
   Eqs = [_ | _],
   maplist(guards, Eqs, Css),
   Css = [Conds | Rest],
   forall(member(Cs, Rest), Cs =@= Conds).

guards(P := where(C, V, E), Conds) :-
   core:place(P, N, Ts), core:place(E, N1, Ts1), N1 == N, Ts1 == Ts,
   ( V = where(_, _, E1), core:place(E1, N2, Ts2), N2 == N, Ts2 == Ts -> guards(P := V, Cs), Conds = [C | Cs]
   ; Conds = [C] ).

% direct_bound(+Conds, +Is, +Axis, +B0, -B): the bounds of the axis from the guards comparing
% it with a term free of the box's axes.
direct_bound(Conds, Is, I:E, B0, [I-lo(Lo)-hi(Hi) | B0]) :-
   foldl(bound_of(I, Is), Conds, 0-(E-1), Lo-Hi).

bound_of(I, Is, C, Lo0-Hi0, LH), C =.. [Op, A, B], B == I, free_of(Is, A), lower(Op, A, L) =>
   LH = max(Lo0, L)-Hi0.
bound_of(I, Is, C, Lo0-Hi0, LH), C =.. [Op, A, B], A == I, free_of(Is, B), upper(Op, B, H) =>
   LH = Lo0-min(Hi0, H).
bound_of(_, _, _, LH0, LH) =>
   LH = LH0.

lower(<, A, L) => L = A + 1.
lower(=<, A, L) => L = A.
upper(<, B, H) => H = B - 1.
upper(=<, B, H) => H = B.

free_of(Is, T) :-
   term_variables(T, Vs),
   \+ ( member(V, Vs), in_list(Is, V) ).

% between_axes(+Conds, +Axis, +B0, -B): a guard J < I or J =< I between two axes lifts the
% lower bound of I to J's and lowers the upper bound of J to I's.
between_axes(Conds, I:_, B0, B) :-
   foldl(axes_bound(I), Conds, B0, B).

axes_bound(I, C, B0, B), C =.. [Op, J, I1], I1 == I, var(J), bound(B0, J, lo(LoJ)) =>
   lower(Op, LoJ, L), raise(B0, I, lo, L, B).
axes_bound(I, C, B0, B), C =.. [Op, I1, J], I1 == I, var(J), bound(B0, J, hi(HiJ)) =>
   upper(Op, HiJ, H), raise(B0, I, hi, H, B).
axes_bound(_, _, B0, B) =>
   B = B0.

bound(Bounds, I, lo(Lo)) :- member(I1-lo(Lo)-_, Bounds), I1 == I, !.
bound(Bounds, I, hi(Hi)) :- member(I1-_-hi(Hi), Bounds), I1 == I, !.

raise([I1-lo(Lo)-hi(Hi) | B0], I, lo, L, B), I1 == I => B = [I-lo(max(Lo, L))-hi(Hi) | B0].
raise([I1-lo(Lo)-hi(Hi) | B0], I, hi, H, B), I1 == I => B = [I-lo(Lo)-hi(min(Hi, H)) | B0].
raise([X | B0], I, Which, V, B) => B = [X | B1], raise(B0, I, Which, V, B1).
raise([], _, _, _, B) => B = [].

% strip_range(+Bounds, +Axis, +Width-Mult, +R0, -R): the range of the axis in strips of Width,
% rounded out to Mult strips, left out when it is the whole axis.
strip_range(Bounds, I:E, T-Mult, R0, R) :-
   bound(Bounds, I, lo(Lo)), bound(Bounds, I, hi(Hi)),
   fold_term(Lo, Lo1), fold_term(Hi, Hi1),
   (  Lo1 == 0, Hi1 == E - 1
   -> R = R0
   ;  Block is T*Mult,
      R = [I-range((Lo1 // Block)*Mult, ((Hi1 // Block) - (Lo1 // Block) + 1)*Mult) | R0]
   ).

% fold_term(+T0, -T): T0 with its ground arithmetic evaluated.
fold_term(T0, T), ground(T0) => T is T0.
fold_term(T0, T), compound(T0) => T0 =.. [F | As0], maplist(fold_term, As0, As), T =.. [F | As].
fold_term(T0, T) => T = T0.

% staging(+Box, +Par, +Seq1, +TilePairs, +Written, +Priv, +Locals, +Tile, +G, +TK, -Stage): the
% kernel is a loop over one axis K around tile loops, its last two work-item axes are strips,
% any leading ones batch axes, each written name is private, and every read of K is affine in
% K, the batch axes, and at most one axis and its strip: then the work-groups are G*G items of
% one batch point, and each such read is staged in local memory per block of TK of K:
% stage(TK, Tiles), a tile(Read, Axis, Strip, Major, Name) per read, laid out with K last, or
% K first when its strip is the last tile loop, for a vector along it.
% With threads(T), a CPU: each of T work items, one per core, owns a slice of the second strip
% of one batch point and runs the BLAS loop nest in plain C: per chunk of the slice whose
% panel fits local memory, per block of KC of K it packs the reads of the chunk into a panel,
% per block of MC rows it packs the reads of those rows, and runs the register micro-kernel
% over the whole block for each tile of the chunk. No work-group, no barrier.
staging(Box, Par, [K:D], TilePairs, Written, Priv, [], _, _, _, Threads0, KC0, MC0, LDS, Stage),
      Threads0 > 0, append(Batch, [I:PI, J:PJ], Par), maplist(arg(1), Batch, BatchIs),
      \+ ( member(B, BatchIs), member(B1-_, TilePairs), B1 == B ),
      ground(PI-PJ-D), extent(PI, NI), extent(PJ, NJ), extent(D, N),
      member(I1-Ii, TilePairs), I1 == I, member(J1-Jj, TilePairs), J1 == J,
      length(Written, NW), length(Priv, NW),
      Box = over(Axes, Eqs), \+ ( member(E, Eqs), is_box(E) ),
      core:extent(Axes, Ii, EI), core:extent(Axes, Jj, EJ), extent(EI, TI), extent(EJ, TJ),
      block(N, KC0, KC), MCT0 is max(1, MC0 // TI), block(NI, MCT0, MCT), block(NJ, Threads0, Threads),
      reads(Box, Written, Reads),
      include(mentions_k(K), Reads, Staged),
      maplist(staged(I-Ii-TI-k_last, J-Jj-TJ, K, BatchIs), Staged, Tiles0) =>
   foldl(tile_name, Tiles0, 0-[], _-Tiles),
   NS is NJ // Threads,
   Most is max(1, (LDS // 4 - MCT*TI*KC - KC) // (TJ*KC)),
   aggregate_all(max(C), ( between(1, Most, C), NS mod C =:= 0 ), NSC),
   Stage = pack(Threads, KC, MCT, NS, NSC, Tiles).
staging(Box, Par, [K:D], TilePairs, Written, Priv, [], G, TK0, Major, _, _, _, _, Stage),
      TK0 > 0, append(Batch, [I:PI, J:PJ], Par), maplist(arg(1), Batch, BatchIs),
      \+ ( member(B, BatchIs), member(B1-_, TilePairs), B1 == B ),
      ground(PI-PJ-D), extent(PI, NI), extent(PJ, NJ), extent(D, N), NI mod G =:= 0, NJ mod G =:= 0, block(N, TK0, TK),
      member(I1-Ii, TilePairs), I1 == I, member(J1-Jj, TilePairs), J1 == J,
      length(Written, NW), length(Priv, NW),
      Box = over(Axes, Eqs), \+ ( member(E, Eqs), is_box(E) ),
      core:extent(Axes, Ii, EI), core:extent(Axes, Jj, EJ), extent(EI, TI), extent(EJ, TJ),
      reads(Box, Written, Reads),
      include(mentions_k(K), Reads, Staged),
      maplist(staged(I-Ii-TI-Major, J-Jj-TJ, K, BatchIs), Staged, Tiles0) =>
   foldl(tile_name, Tiles0, 0-[], _-Tiles),
   Stage = stage(G, TK, Tiles).
staging(_, _, _, _, _, _, _, _, _, _, _, _, _, _, Stage) =>
   Stage = none.

mentions_k(K, R) :-
   mentions(R, K).

% block(+N, +TK0, -TK): the largest block of K up to TK0 that divides N, at least 2.
block(N, TK0, TK) :-
   aggregate_all(max(T), ( between(2, TK0, T), N mod T =:= 0 ), TK).

% reads(+Box, +Written, -Reads): the distinct reads of names not written in Box.
reads(Box, Written, Reads) :-
   read_terms(Box, Written, Reads0, []),
   dedupe(Reads0, Reads).

read_terms(T, _, Rs0, Rs), var(T) => Rs0 = Rs.
read_terms(T, W, Rs0, Rs), core:place(T, N, S), \+ in_list(W, N) => Rs0 = [T | Rs1], read_terms(S, W, Rs1, Rs).
read_terms(T, W, Rs0, Rs), compound(T) => T =.. [_ | As], foldl([A, R0, R]>>read_terms(A, W, R0, R), As, Rs0, Rs).
read_terms(_, _, Rs0, Rs) => Rs0 = Rs.

dedupe([], []).
dedupe([R | Rs0], [R | Rs]) :-
   exclude(==(R), Rs0, Rs1),
   dedupe(Rs1, Rs).

% staged(+I-Ii-TI, +J-Jj-TJ, +K, +BatchIs, +Read, -Tile): Read mentions K, batch indices, and
% the axes of one strip, or none: tile(Read, Axis, Strip, Width, Major, Name).
staged(I-Ii-TI-Major, _, K, Bs, R, Tile), within(R, [I, Ii, K | Bs]) => Tile = tile(R, I, Ii, TI, Major, _).
staged(_, J-Jj-TJ, K, Bs, R, Tile), within(R, [J, Jj, K | Bs]) => Tile = tile(R, J, Jj, TJ, k_first, _).
staged(_, _, K, Bs, R, Tile), within(R, [K | Bs]) => Tile = tile(R, none, none, 1, k_last, _).
staged(_, _, _, _, _, _) => fail.

within(R, Allowed) :-
   core:place(R, _, Subs),
   term_variables(Subs, Vs),
   forall(member(V, Vs), in_list(Allowed, V)).

tile_name(tile(R, A, S, T, M, Name), N0-Ts0, N-Ts) :-
   format(atom(Name), "s~d", [N0]),
   N is N0+1,
   Ts = [tile(R, A, S, T, M, Name) | Ts0].

axis_in(Is, I:_) :-
   in_list(Is, I).

% parallel_axes(+Box, +Locals, +Axes, +Strict, +Fill, +L, -Par): the strictly parallel axes,
% or, when they hold fewer points than fill the device, Min groups of L items, and the
% other axes would loop more than a group's worth, every axis parallel with atomic
% updates: a scatter runs its sources in parallel, and so does an embedding's backward with
% its few columns; a reduction with enough outputs, or a short one, keeps its axis a loop.
parallel_axes(Box, Locals, Axes, Strict, Fill, L, Par) :-
   maplist(arg(2), Strict, Es), size(Es, N),
   include(parallel(Box, Locals, atomic), Axes, Atomic),
   maplist(arg(2), Atomic, AEs), size(AEs, NA),
   (  N < Fill, NA > N*L
   -> Par = Atomic
   ;  Par = Strict
   ).

% locals(+Out, +Boxes, +Box, -Locals): the names written in the inner boxes of Box alone, and
% mentioned by no other box.
locals(Out, Boxes, over(_, Eqs), Locals) :-
   partition(is_box, Eqs, Inner, Top),
   core:writes(over([], Inner), Written),
   core:writes(over([], Top), Direct),
   include(local(Out, Boxes, Direct), Written, Locals).

is_box(over(_, _)).

local(Out, Boxes, Direct, N) :-
   N \== Out,
   \+ in_list(Direct, N),
   boxes_of(N, [_]),
   \+ ( member(B, Boxes), names(B, Ns), in_list(Ns, N), \+ ( core:writes(B, Ws), in_list(Ws, N) ) ).

% parallel(+Box, +Locals, +Axis): no written name but a local one is accessed at places that
% differ along Axis: where two accesses differ, neither mentions it, and where all agree,
% some subscript covers it, so that two points of the axis never meet.
parallel(Box, Locals, Axis) :-
   parallel(Box, Locals, strict, Axis).

% parallel(+Box, +Locals, +How, +Axis): with How atomic, a name only ever folded into by a
% monoid, G[Ts] := Op(G[Ts], E), needs no cover: two points that meet are folded by an
% atomic update, in whatever order.
parallel(Box, Locals, How, D:_) :-
   Box = over(Axes, _),
   core:writes(Box, Written),
   forall(( member(G, Written), \+ in_list(Locals, G) ),
          ( accesses(Box, G, [S | Ss]),
            forall(member(S1, Ss), compatible(D, S, S1)),
            ( How == atomic, folded(Box, G, _)
            -> true
            ;  agreed(S, Ss, Agreed),
               member(Sub, Agreed),
               covers(Axes, Sub, D) ) )).

% folded(+Box, +G, -Op): every equation writing G in Box is G[Ts] := Op(G[Ts], E), one monoid
% Op, E not reading G, and G is read nowhere else in Box.
folded(over(_, Eqs), G, Op) :-
   include(writes_name(G), Eqs, Ws),
   Ws = [_ | _],
   maplist(fold_of(G), Ws, Ops),
   Ops = [Op | Rest], forall(member(O, Rest), O == Op),
   accesses(over([], Eqs), G, Ss),
   length(Ws, NW), length(Ss, NS), NS =:= 2*NW.

writes_name(G, P := _) :- core:place(P, G1, _), G1 == G.
writes_name(G, over(_, Eqs)) :- member(E, Eqs), writes_name(G, E), !.

fold_of(G, P := V, Op) :-
   core:place(P, G1, Ts), G1 == G,
   V =.. [Op, R, E], monoid(Op, _),
   core:place(R, G2, Ts1), G2 == G, Ts1 == Ts,
   names(E, Ns), \+ in_list(Ns, G).

% atomics(+Box, +Par, +Locals, -Atomics): the folded names whose targets do not cover every
% parallel axis: their updates are atomic. Name-Op pairs.
atomics(Box, Par, Locals, Atomics) :-
   Box = over(Axes, _),
   core:writes(Box, Written),
   convlist(atomic_name(Box, Axes, Par, Locals), Written, Atomics).

atomic_name(Box, Axes, Par, Locals, G, G-Op) :-
   \+ in_list(Locals, G),
   folded(Box, G, Op),
   accesses(Box, G, [S | _]),
   member(D:_, Par), \+ ( member(Sub, S), covers(Axes, Sub, D) ), !.

compatible(D, S, S1) :-
   forall(( nth0(P, S, X), nth0(P, S1, Y), X \== Y ),
          ( \+ mentions(X, D), \+ mentions(Y, D) )).

% agreed(+S, +Ss, -Agreed): the subscripts of S that every list of Ss has at the same position.
agreed([], _, Agreed) => Agreed = [].
agreed([X | S], Ss, Agreed), maplist(head_tail, Ss, Ys, Ss1), forall(member(Y, Ys), Y == X) =>
   Agreed = [X | Agreed1],
   agreed(S, Ss1, Agreed1).
agreed([_ | S], Ss, Agreed) =>
   maplist(head_tail, Ss, _, Ss1),
   agreed(S, Ss1, Agreed).

head_tail([Y | T], Y, T).

mentions(T, D) :-
   term_variables(T, Vs),
   in_list(Vs, D).

% accesses(+Term, +G, -Subscripts): the subscript lists of every write and read of G in Term,
% sharing their variables with Term.
accesses(Term, G, Ss) :-
   places(G, Term, Ss, []).

places(G, T, Ss0, Ss), var(T), T == G, shape(G, []) => Ss0 = [[] | Ss].
places(_, T, Ss0, Ss), var(T) => Ss0 = Ss.
places(G, T, Ss0, Ss), core:place(T, G1, S), G1 == G => Ss0 = [S | Ss1], places(G, S, Ss1, Ss).
places(G, T, Ss0, Ss), compound(T) => T =.. [_ | As], foldl(places(G), As, Ss0, Ss).
places(_, _, Ss0, Ss) => Ss0 = Ss.

% covers(+Axes, +S, +D): S is a read of a permutation, see core:permutation/1, at subscripts
% one of which covers D, so distinct along D; or S is affine in the indices of Axes, its
% coefficients a mixed radix,
% so that it takes a different value at each point of the axes it mentions, D among them.
covers(Axes, S, D) :-
   core:place(S, P, Es), get_attr(P, perm, _),
   !,
   member(E, Es), covers(Axes, E, D),
   !.
covers(Axes, S, D) :-
   catch(core:form(Axes, S, 1, 0-[], _-Pairs), error(_, _), fail),
   \+ ( member(Key-_, Pairs), nonvar(Key) ),      % a remainder covers nothing
   keysort(Pairs, Sorted),
   group_pairs_by_key(Sorted, Groups),
   maplist(radix(Axes), Groups, Radix0),
   exclude(==(none), Radix0, Radix),
   member(I-_-_, Radix), I == D,
   maplist([J-K-N, A-(J-K-N)]>>(A is abs(K)), Radix, Keyed),
   keysort(Keyed, ByCoef),
   pairs_values(ByCoef, Ordered),
   foldl(mixed, Ordered, 0, _).

% radix(+Axes, +Group, -Term): I-K-N for an index term, N the most its extent can be, inf
% without an upper bound, which reaches past every later term; none for a term that sums to 0.
radix(_, _-Ks, Term), sum_list(Ks, 0) => Term = none.
radix(Axes, I-Ks, Term) =>
   sum_list(Ks, K),
   core:extent(Axes, I, E),
   (  extent_max(E, N)
   -> true
   ;  N = inf
   ),
   Term = I-K-N.

mixed(_-K-N, Reach0, Reach) :-
   Reach0 < abs(K),
   Reach is Reach0 + abs(K)*(N-1).

% tiles_of(+Tile, +Axes, -Widths): the tile width of each axis: Tile, or its own from a list,
% which applies to the last axes, 1 for the leading axes beyond the list: batch axes.
tiles_of(Tile, Axes, Widths), integer(Tile) => length(Axes, N), length(Widths, N), maplist(=(Tile), Widths).
tiles_of(Tiles, Axes, Widths) =>
   length(Axes, N), length(Widths, N), length(Tiles, M), Extra is max(0, N - M),
   length(Ones, Extra), maplist(=(1), Ones), append(Ones, Tiles, Padded), append(_, Widths, Padded).

% strip(+Tile-Axis, +Box0-Tiles0, -Box-Tiles): the axis I:N, when Tile divides N, is split
% into I:N/Tile, a work item, and Ii:Tile, a loop: the old I is I*Tile + Ii.
strip(Tile-(I:E), over(Axes0, Eqs0)-Tiles0, BT), ground(E), extent(E, N), Tile > 1, N > Tile, N mod Tile =:= 0 =>
   No is N // Tile,
   subst([I-(I*Tile + Ii)], Eqs0, Eqs),
   replace_axis(Axes0, I, I:No, Axes1),
   append(Axes1, [Ii:Tile], Axes),
   BT = over(Axes, Eqs)-[I-Ii | Tiles0].
strip(_, BT0, BT) =>
   BT = BT0.

% replace_axis(+Axes0, +I, +Axis, -Axes): the axis of the index I, found by identity, replaced.
replace_axis([I0:_ | Axes], I, Axis, Axes1), I0 == I => Axes1 = [Axis | Axes].
replace_axis([A | Axes0], I, Axis, Axes1) => Axes1 = [A | Axes], replace_axis(Axes0, I, Axis, Axes).

% private(+Box, +ParIs, +TilePairs, +G, -G-Infos): every access of G is the same subscript
% list, depending on work item and tile indices alone, and covering each tile index it
% mentions: an info(Ii, T, P, I) per tile index Ii of width T, found at position P of the
% subscripts beside its work-item index I.
private(Box, ParIs, TilePairs, G, G-Infos) :-
   accesses(Box, G, [S | Ss]),
   forall(member(S1, Ss), S1 == S),
   term_variables(S, Vs),
   pairs_values(TilePairs, TileIs),
   append(ParIs, TileIs, Allowed),
   forall(member(V, Vs), in_list(Allowed, V)),
   Box = over(BoxAxes, _),
   include(in_list(Vs), TileIs, Mentioned),
   maplist(tile_info(S, BoxAxes, TilePairs), Mentioned, Infos).

tile_info(S, BoxAxes, TilePairs, Ii, info(Ii, T, P, I)) :-
   core:extent(BoxAxes, Ii, E),
   extent(E, T),
   member(I-Ii1, TilePairs), Ii1 == Ii, !,
   nth0(P, S, Sp), mentions(Sp, Ii), !,
   covers(BoxAxes, Sp, Ii).

info_axis(info(Ii, T, _, _), Ii:T).
info_width(info(_, T, _, _), T).

% Printing
% ========

% source(+Kernels, -Source): the OpenCL C of Kernels, named k0, k1, ..., after the atomic
% folds on floats they use, compare-and-swap loops, as OpenCL C has none built in.
source(Plan, Source) :-
   flat_plan(Plan, Kernels),
   foldl([K, S0, S]>>(get_dict(id, K, I), kernel_source(I, K, S1), string_concat(S0, S1, S)), Kernels, "", Body),
   foldl([K, Os0, Os]>>(get_dict(atomics, K, As) -> maplist(typed_atomic, As, Ops), append(Os0, Ops, Os) ; Os = Os0),
         Kernels, [], Ops0),
   sort(Ops0, Ops),
   foldl([Op, H0, H]>>(atomic_helper(Op, H1), string_concat(H0, H1, H)), Ops, "", Helpers),
   string_concat(Helpers, Body, Source).

typed_atomic(G-Op, Op-T) :-
   ctype(G, T).

% atomic_helper(+Op-T, -Helper): the float folds, and the int product, loop on a compare-and-swap;
% the other int folds are built in.
atomic_helper(Op-float, Helper) =>
   atomic_function(Op, float, F), fold(Op, float, 'old.f', 'v', Expr),
   format(string(Helper), "inline void ~w(volatile __global float *p, float v) {
  union { unsigned int u; float f; } old, new_;
  do { old.f = *p; new_.f = ~w; } while (atomic_cmpxchg((volatile __global unsigned int *)p, old.u, new_.u) != old.u);
}

", [F, Expr]).
atomic_helper((*)-int, Helper) =>
   Helper = "inline void atomic_mul_int(volatile __global int *p, int v) {
  int old;
  do { old = *p; } while (atomic_cmpxchg(p, old, old * v) != old);
}

".
atomic_helper(_, Helper) =>
   Helper = "".

kernel_source(I, K, Source), get_dict(kind, K, items) =>
   kernel{box: Box, par: Par, seq: Seq, priv: Priv, local: Local, names: Names0, stage: Stage, vector: W, ranges: Ranges,
          atomics: Atomics, pre: Pre, post: Post, temps: Temps} :< K,
   Box = over(_, Eqs),
   context(K, Box, Priv, Local, Ctx0),
   get_dict(tiles, K, TilePairs), pairs_values(TilePairs, TileIs),
   core:writes(over([], Pre), Inits0), core:writes(over([], Post), Inits1), append(Inits0, Inits1, Inits),
   epilogue_names(Post, Priv, Priv1),
   Ctx = Ctx0.put(_{stage: [], vector: W, vec: none, unroll: TileIs, ranges: Ranges, atomics: Atomics,
                   pre: Pre, post: Post, temps: Temps, inits: Inits, priv: Priv1}),
   exclude(in_list(Temps), Names0, Names),
   items_code(Ctx, Par, Seq, Eqs, Stage, Codes),
   kernel_text(I, Ctx, Names, Codes, Source).

% epilogue_names(+Post, +Priv0, -Priv): the names the epilogue writes at the register tile's
% point share its register layout.
epilogue_names(Post, Priv0, Priv) :-
   core:writes(over([], Post), Ws),
   ( Priv0 = [_-Infos | _] -> convlist(as_tile(Infos, Priv0), Ws, New), append(Priv0, New, Priv) ; Priv = Priv0 ).

as_tile(Infos, Priv0, N, N-Infos) :-
   \+ ( member(N1-_, Priv0), N1 == N ).
kernel_source(I, K, Source), get_dict(kind, K, groups) =>
   kernel{rows: Rows, phases: Phases, local: L, names: Names, shared: Shared} :< K,
   context(K, none, [], [], Ctx0),
   phase_writes(Phases, Written),
   ( forall(member(N, Written), ( member(N1-_-_, Shared), N1 == N )) -> Fence = local ; Fence = global ),
   Ctx = Ctx0.put(_{shared: Shared, fence: Fence, items: L}),
   ( get_dict(item, K, true) -> Items = item ; Items = L ),
   phrase(( work_groups(Ctx, Rows, Items), sequence(shared_decl(Ctx), Shared),
            sequence(shared_copy(Ctx, L, Rows, in), Shared), shared_fence(Ctx, Shared),
            sequence(phase_code(Ctx, L), Phases),
            sequence(shared_copy(Ctx, L, Rows, out), Shared) ), Codes),
   kernel_text(I, Ctx, Names, Codes, Source).

% phase_writes(+Phases, -Names): the names the phases write.
phase_writes(Phases, Names) :-
   foldl(phase_write, Phases, [], Names0),
   list_to_set(Names0, Names).

phase_write(loop(_, _, Phases), Acc0, Acc) => foldl(phase_write, Phases, Acc0, Acc).
phase_write(serial(Eqs), Acc0, Acc) => core:writes(over([], Eqs), Ws), append(Acc0, Ws, Acc).
phase_write(spread(_, _, Eqs), Acc0, Acc) => core:writes(over([], Eqs), Ws), append(Acc0, Ws, Acc).
phase_write(reduce(_, Reds), Acc0, Acc) => maplist(arg(1), Reds, Ws), append(Acc0, Ws, Acc).

shared_decl(Ctx, N-_-Size) -->
   { var_name(Ctx, N, Name), format(atom(SName), "s_~w", [Name]), ctype(N, T) },
   local_array(T, SName, Size).

% local_array(+T, +Name, +Size): a local array of Size elements of T, aligned to 32 bytes at run
% time: a vector access to it is a typed pointer, aligned loads, and a runtime may hand local
% memory out aligned to 16 bytes only, whatever the attribute asks (pocl's OpenMP scheduler
% takes it from malloc, and lays the first array at the raw base), which faults the loads.
local_array(T, Name, Size) -->
   { Padded is Size + 8 },
   fmt("  __local ~w ~w_[~d] __attribute__((aligned(32)));\n", [T, Name, Padded]),
   fmt("  __local ~w *~w = (__local ~w *)(((uintptr_t)~w_ + 31) & ~~(uintptr_t)31);\n", [T, Name, T, Name]).

% tile_type(+R, -T): the C type of a staged tile of the read R, float: the staged and vectorised
% kernels take float elements.
tile_type(R, T) :-
   core:place(R, N, _),
   ctype(N, T),
   (  T == float
   -> true
   ;  domain_error(kind(float), R)
   ).

shared_fence(_, []) --> [].
shared_fence(Ctx, [_ | _]) --> fence(Ctx).

% The slice of the group's row point: at g*Size in the buffer, g the group id, 0 without rows.
shared_copy(Ctx, L, Rows, Way, N-_-Size) -->
   { var_name(Ctx, N, Name), row_id(Rows, G), copy_way(Way, Name, G, Size, Lhs, Rhs) },
   fmt("  for (int e = l; e < ~d; e += ~d) ~w = ~w;\n", [Size, L, Lhs, Rhs]).

copy_way(in, Name, G, Size, Lhs, Rhs) =>
   format(atom(Lhs), "s_~w[e]", [Name]), format(atom(Rhs), "~w[~w * ~d + e]", [Name, G, Size]).
copy_way(out, Name, G, Size, Lhs, Rhs) =>
   format(atom(Lhs), "~w[~w * ~d + e]", [Name, G, Size]), format(atom(Rhs), "s_~w[e]", [Name]).

row_id([], G) => G = '0'.
row_id(_, G) => G = g.

context(K, Box, Priv, Local, Ctx) :-
   kernel_variables(K, Vars),
   foldl([V, J-Ns0, J1-[V-Name | Ns0]]>>(format(atom(Name), "v~d", [J]), J1 is J+1), Vars, 0-[], _-Env),
   get_dict(free, K, Free),
   get_dict(extents, K, Extents),
   item_indices(K, Items),
   Ctx = ctx{env: Env, box: Box, priv: Priv, local: Local, stage: [], vector: 1, vec: none, unroll: [], free: Free,
             extents: Extents, pars: Items, ranges: [], shared: [], fence: global, items: 0, temps: [], atomics: [],
             pre: [], post: [], inits: []}.

% item_indices(+K, -Is): the indices a work item of K fixes: its parallel axes, or its row.
item_indices(K, Is), get_dict(par, K, Par) => maplist(arg(1), Par, Is).
item_indices(K, Is), get_dict(rows, K, Rows) => maplist(arg(1), Rows, Is).
item_indices(_, Is) => Is = [].

% fixed_indices(+Ctx, -Is): the indices fixed in a kernel: the work item's and the host loops'.
fixed_indices(Ctx, Is) :-
   get_dict(pars, Ctx, Pars),
   get_dict(free, Ctx, Free),
   append(Pars, Free, Is).

% private_extents(+Ctx, +N, -Es): the extents of the private array of the local name N, the
% slice a work item touches: at each position, one more than the most its subscripts reach
% over the kernel's loops with the fixed indices at 0; 1 where the item alone subscripts.
private_extents(Ctx, N, Es) :-
   get_dict(box, Ctx, Box),
   all_axes(Box, Axes),
   fixed_indices(Ctx, Fixed),
   exclude(axis_in(Fixed), Axes, Scope),
   accesses(Box, N, Ss),
   maplist(private_coords(Ctx), Ss, Cs),
   shape(N, Shape),
   length(Shape, Rank),
   findall(P, between(1, Rank, P), Ps),
   maplist(private_extent(Scope, Cs), Ps, Es).

private_extent(Scope, Cs, P, E) :-
   maplist(nth1(P), Cs, Cps),
   maplist(reach(Scope), Cps, Reaches),
   max_list(Reaches, Most),
   E is Most + 1.

% reach(+Scope, +C, -R): the most the coordinate C is over Scope, a number: a private array has a
% size.
reach(Scope, C, R) :-
   core:hull(Scope, C, _, Hi),
   (  extent_max(Hi, R)
   -> true
   ;  existence_error(upper_bound, C)
   ).

% all_axes(+Box, -Axes): the axes of Box and of the boxes inside it.
all_axes(over(Axes0, Eqs), Axes) :-
   include(is_box, Eqs, Inner),
   maplist(all_axes, Inner, Axess),
   append([Axes0 | Axess], Axes).

% private_coords(+Ctx, +Ts, -Cs): the subscripts Ts with the fixed indices at 0.
private_coords(Ctx, Ts, Cs) :-
   fixed_indices(Ctx, Fixed),
   maplist([V, V-0]>>true, Fixed, Pairs),
   subst(Pairs, Ts, Cs).

% kernel_variables(+K, -Vars): the variables of the kernel K and of the shapes of its names.
kernel_variables(K, Vars) :-
   get_dict(names, K, Names),
   maplist(shape, Names, Shapes),
   term_variables(K-Shapes, Vars).

% kernel_extents(+K, -Extents): the unknown extents the kernel K mentions, its int parameters,
% recorded on the kernel when the plan is numbered, before a run binds them.
kernel_extents(K, Extents) :-
   kernel_variables(K, Vars),
   include(is_extent, Vars, Extents).

is_extent(V) :-
   get_attr(V, clpBNR, _).

% items_code(+Ctx, +Par, +Seq, +Eqs, +Stage, -Codes): without staging, the work item unravels
% its id and runs the loops. With it, the work-group is a G*G block of items over the two
% strips; per block of TK of the K axis the items load the staged tiles together, and each
% runs the tile loops on them.
items_code(Ctx, Par, Seq, Eqs, none, Codes) =>
   tile_axes(Ctx, Seq, Tiles),
   phrase(( work_items(Ctx, Par), privates(Ctx), prologue(Ctx, copy_in), pre(Ctx, Tiles), loops(Ctx, Seq, Eqs),
            post(Ctx, Tiles), prologue(Ctx, copy_out) ), Codes).

% tile_axes(+Ctx, +Seq, -Tiles): the tile loops among the sequential axes.
tile_axes(Ctx, Seq, Tiles) :-
   get_dict(unroll, Ctx, TileIs),
   include(axis_in(TileIs), Seq, Tiles).
items_code(Ctx0, Par, [K:D | Tiles], Eqs0, stage(G, TK, Tiles0), Codes), append(Batch, [I:PI, J:PJ], Par) =>
   hoist_masks(Ctx0, K, Eqs0, Ctx2, Eqs, Epilogue),
   fresh(Ctx2, [Li-li, Lj-lj, Gi-gi, Gj-gj, Vv-v, Kb-kb, Kk-kk], Ctx1),
   maplist(tile_index(I-Li, J-Lj, Kk, TK, G), Tiles0, Tiles1),
   Ctx = Ctx1.put(stage, Tiles1),
   extent(PI, NI), GI is NI // G, extent(PJ, NJ), GJ is NJ // G, extent(D, N), Blocks is N // TK, Items is G*G,
   maplist(var_name(Ctx), [I, J, K], [CI, CJ, CK]),
   unroll_pragma(TK, Pragma),
   maplist(load_spec(Ctx, Gi-I, Gj-J, Vv, Kb, K, G, TK, Items), Tiles1, Specs),
   group_ids(Ctx, Batch, I, J, G, GI, GJ, GroupIds),
   phrase(( fmt("  int l = get_local_id(0);\n  int li = l / ~d;\n  int lj = l % ~d;\n", [G, G]),
            fmt("  size_t g = get_group_id(0);\n~w", [GroupIds]),
            fmt("  int ~w = gi * ~d + li;\n  int ~w = gj * ~d + lj;\n", [CI, G, CJ, G]),
            sequence(local_tile(G, TK), Tiles1),
            sequence(prefetch_regs, Specs),
            privates(Ctx), prologue(Ctx, copy_in), pre(Ctx, Tiles),
            "  int kb = 0;\n",
            sequence(vectors(Ctx, Items, fill), Specs),
            "  barrier(CLK_LOCAL_MEM_FENCE);\n",
            fmt("  for (kb = 0; kb < ~d; kb++) {\n  if (kb + 1 < ~d) {\n", [Blocks, Blocks]),
            sequence(vectors(Ctx, Items, prefetch), Specs),
            "  }\n",
            fmt("  ~w\n  for (int kk = 0; kk < ~d; kk++) {\n  int ~w = kb * ~d + kk;\n", [Pragma, TK, CK, TK]),
            loops(Ctx, Tiles, Eqs),
            fmt("  }\n  barrier(CLK_LOCAL_MEM_FENCE);\n  if (kb + 1 < ~d) {\n", [Blocks]),
            sequence(vectors(Ctx, Items, unload), Specs),
            "  }\n  barrier(CLK_LOCAL_MEM_FENCE);\n  }\n",
            loops(Ctx, Tiles, Epilogue), post(Ctx, Tiles),
            prologue(Ctx, copy_out) ), Codes).

% hoist_masks(+Ctx0, +K, +Eqs0, -Ctx, -Eqs, -Epilogue): an equation P := where(C, P + E, P),
% or with -, whose guards are free of the K axis, accumulates E unmasked into a fresh private
% tile over the K loop, and applies the guard once after it: P := where(C, P + T, P). The
% selects leave the micro-kernel, which is then the matmul's.
hoist_masks(Ctx0, K, Eqs0, Ctx, Eqs, Epilogue) :-
   foldl(hoist_mask(K), Eqs0, Ctx0-[]-[], Ctx-Rev-RevE),
   reverse(Rev, Eqs), reverse(RevE, Epilogue).

hoist_mask(K, P := V, Ctx0-Eqs-Eps, Acc1),
      core:place(P, N, Ts), guards(P := V, Conds), \+ mentions(Conds, K),
      innermost(V, Inner), Inner =.. [Op, P1, E], memberchk(Op, [+, -]), core:place(P1, N1, Ts1), N1 == N, Ts1 == Ts,
      get_dict(priv, Ctx0, Priv), member(N2-Infos, Priv), N2 == N =>
   shape(N, Shape), shape(Acc, Shape),
   T = [](Ts, Acc),
   Fold =.. [Op, P, T],
   rebuild(Conds, Fold, P, Masked),
   get_dict(env, Ctx0, Env0), length(Env0, J), format(atom(Name), "v~d", [J]),
   get_dict(temps, Ctx0, Temps),
   Ctx = Ctx0.put(_{env: [Acc-Name | Env0], priv: [Acc-Infos | Priv], temps: [Acc | Temps]}),
   Acc1 = Ctx-[T := T + E | Eqs]-[P := Masked | Eps].
hoist_mask(_, Eq, Ctx-Eqs-Eps, Acc1) =>
   Acc1 = Ctx-[Eq | Eqs]-Eps.

innermost(where(_, V, _), Inner) => innermost(V, Inner).
innermost(V, Inner) => Inner = V.

rebuild([], Fold, _, Masked) => Masked = Fold.
rebuild([C | Cs], Fold, P, Masked) => rebuild(Cs, Fold, P, Inner), Masked = where(C, Inner, P).

% A tile is loaded by vectors of the kernel's width along its inner dimension, when the read
% is contiguous along it, else one element at a time: item l takes the vectors l, l + Items,
% ... The first block fills the tiles directly. Then, while a block is computed, the next
% block's vectors are fetched into registers, and stored to the tiles after the barrier, so
% that the latency of the global loads overlaps the compute.
% load_spec(..., -spec(Name, W, Count, Vectors, Index, Step, Subs, Reg)): vector v of the tile
% Name reads the global subscripts Subs, and lands at element Index, its lanes Step apart:
% 1 when the read is contiguous along the layout's inner dimension, else the length of a row
% when it is contiguous along the other one, a transposed store; Count vectors per item.
load_spec(Ctx, Gi-I, Gj-J, Vv, Kb, K, G, TK, Items, tile(R, Axis, Strip, T, Major, Name, _),
          spec(Name, W, Count, Vectors, Index, Step, Subs1, Reg)) :-
   core:place(R, N, Subs),
   tile_rows(Axis, G, T, Rows),
   get_dict(vector, Ctx, W0),
   access(Ctx, N, Subs, _-Off),
   along(W0, Major, Strip, K, Off, T, TK, Rows, W, Along, Step),
   Vectors is Rows*TK // W,
   Count is (Vectors + Items - 1) // Items,
   group_of(Axis, I, J, Gi, Gj, GP),
   vector_place(Major, Along, Axis, Strip, GP, K, Kb, Vv, W, T, TK, Rows, G, Index, Pairs),
   subst(Pairs, R, Subs1),
   format(atom(Reg), "f_~w", [Name]).

% along(+W0, +Major, +Strip, +K, +Off, +T, +TK, +Rows, -W, -Along, -Step): the vectors run
% along K or along the strip, whichever the read is contiguous in, with the lanes Step apart
% in the tile; one element at a time when neither.
along(W0, k_last, _, K, Off, _, TK, _, W, Along, Step), W0 > 1, TK mod W0 =:= 0, stride(K, Off, 1) =>
   W = W0, Along = k, Step = 1.
along(W0, k_last, Strip, _, Off, T, TK, _, W, Along, Step), W0 > 1, T mod W0 =:= 0, stride(Strip, Off, 1) =>
   W = W0, Along = strip, Step = TK.
along(W0, k_first, Strip, _, Off, T, _, _, W, Along, Step), W0 > 1, T mod W0 =:= 0, stride(Strip, Off, 1) =>
   W = W0, Along = strip, Step = 1.
along(W0, k_first, _, K, Off, _, TK, Rows, W, Along, Step), W0 > 1, TK mod W0 =:= 0, stride(K, Off, 1) =>
   W = W0, Along = k, Step = Rows.
along(_, _, _, _, _, _, _, _, W, Along, Step) =>
   W = 1, Along = k, Step = 1.

% vector_place(+Major, +Along, ...): vector Vv is at element Index of the tile, and reads the
% subscripts with Pairs substituted: the tile is a Rows by TK box, (a, kk), stored a-major
% (K last) or kk-major (K first); the vectors run along kk or along a.
vector_place(Major, Along, Axis, Strip, GP, K, Kb, Vv, W, T, TK, Rows, G, Index, Pairs) :-
   box_of(Along, Vv, W, TK, Rows, A, Kk0),
   layout_of(Major, A, Kk0, TK, Rows, Index),
   strip_of(Axis, Strip, GP, G, T, A, Pairs0),
   Pairs = [K-(Kb*TK + Kk0) | Pairs0].

box_of(k, Vv, W, TK, _, A, Kk0) => PerRow is TK // W, A = Vv // PerRow, Kk0 = (Vv mod PerRow)*W.
box_of(strip, Vv, W, _, Rows, A, Kk0) => PerRow is Rows // W, A = (Vv mod PerRow)*W, Kk0 = Vv // PerRow.

layout_of(k_last, A, Kk0, TK, _, Index) => Index = A*TK + Kk0.
layout_of(k_first, A, Kk0, _, Rows, Index) => Index = Kk0*Rows + A.

strip_of(none, _, _, _, _, _, Pairs) => Pairs = [].
strip_of(Axis, Strip, GP, G, T, A, Pairs) => Pairs = [Axis-(GP*G + A // T), Strip-(A mod T)].

prefetch_regs(spec(_, W, Count, _, _, _, _, Reg)) -->
   { vec_type(W, Type) },
   fmt("  ~w ~w[~d];\n", [Type, Reg, Count]).

vec_type(1, Type) => Type = float.
vec_type(W, Type) => format(atom(Type), "float~d", [W]).

% vectors(+Ctx, +Items, +What, +Spec): the loop over an item's vectors: filled into the tile,
% prefetched into the registers from the next block, or unloaded from them into the tile.
vectors(Ctx, Items, What, spec(Name, W, Count, Vectors, Index, Step, Subs, Reg)) -->
   { statement_of(What, Ctx, W, Index, Step, Subs, Name, Reg, Statement) },
   fmt("  #pragma unroll\n  for (int i = 0; i < ~d; i++) { int v = l + i * ~d; if (v < ~d) { ~w } }\n",
       [Count, Items, Vectors, Statement]).

statement_of(fill, Ctx, W, Index, Step, Subs, Name, _, Statement) =>
   index(Ctx, Index, CI), vector_read(Ctx, W, Subs, Read), tile_write(W, Step, Name, CI, Read, Statement).
statement_of(prefetch, Ctx, W, _, _, Subs, _, Reg, Statement) =>
   next_block(Ctx, Subs, Subs1), vector_read(Ctx, W, Subs1, Read), format(atom(Statement), "~w[i] = ~w;", [Reg, Read]).
statement_of(unload, Ctx, W, Index, Step, _, Name, Reg, Statement) =>
   index(Ctx, Index, CI), format(atom(Val), "~w[i]", [Reg]), tile_write(W, Step, Name, CI, Val, Statement).

% tile_write(+W, +Step, +Name, +CI, +Val, -Statement): the W lanes of Val stored at CI, as a
% vector when Step is 1, else one lane per Step elements: the transposed store.
tile_write(W, 1, Name, CI, Val, Statement) =>
   vector_write(W, Name, CI, Val, Statement).
tile_write(W, Step, Name, CI, Val, Statement) =>
   Last is W - 1, numlist(0, Last, Lanes),
   foldl([Lane, S0, S]>>(format(atom(S), "~w ~w[~w + ~d] = t.s~d;", [S0, Name, CI, Lane*Step, Lane])), Lanes, '', Stores),
   format(atom(Statement), "{ float~d t = ~w;~w }", [W, Val, Stores]).

next_block(Ctx, Subs, Subs1) :-
   get_dict(env, Ctx, Env), member(Kb-kb, Env), !,
   subst([Kb-(Kb + 1)], Subs, Subs1).

% vector_read(+Ctx, +W, +Read, -C): the global read R[Subs] as W lanes from its address.
vector_read(Ctx, W, R, C) :-
   core:place(R, N, Subs),
   access(Ctx, N, Subs, Name-Off), index(Ctx, Off, CO),
   lanes_read(W, Name, CO, C).

% A vector access is a typed pointer into the array, in its address space: vloadn and vstoren
% promise only the alignment of a float, and a compiler splits them into lanes; a vector offset
% here is a multiple of the width, as the strips are.
lanes_read(1, Name, CO, C) => format(atom(C), "~w[~w]", [Name, CO]).
lanes_read(W, Name, CO, C) => space(Name, Space), format(atom(C), "(*(~wfloat~d *)&~w[~w])", [Space, W, Name, CO]).

vector_write(1, Name, CI, Val, Statement) => format(atom(Statement), "~w[~w] = ~w;", [Name, CI, Val]).
vector_write(W, Name, CI, Val, Statement) =>
   space(Name, Space), format(atom(Statement), "*(~wfloat~d *)&~w[~w] = ~w;", [Space, W, Name, CI, Val]).

space(Name, Space), sub_atom(Name, 0, 2, _, 'r_') => Space = ''.
space(Name, Space), sub_atom(Name, 0, 2, _, 'p_') => Space = ''.
space(Name, Space), sub_atom(Name, 0, 1, _, s) => Space = '__local '.
space(_, Space) => Space = '__global '.

% The packed kernel: thread t owns the tiles [t*NS, (t+1)*NS) of the second strip and all of
% the first. Per block kb of KC: the panel of each read of the second strip, laid out
% [jp][k][jj]; per block mb of MCT tiles of the first strip: the panel of each read of the
% first strip, laid out [ip][k][ii]; then per tile (jp, ip) of the block: the register tile in,
% the micro-kernel over k, the register tile out. The panels are the work item's own local
% memory: the kernel is launched in work-groups of one.
items_code(Ctx0, Par, [K:D | Tiles], Eqs, pack(Threads, KC, MCT, NS, NSC, Tiles0), Codes), append(Batch, [I:PI, J:_], Par) =>
   fresh(Ctx0, [T-t, Kb-kb, Mb-mb, Jc-jc, Jp-jp, Ip-ip, Kk-k, Ii1-ii, Jj1-jj], Ctx1),
   maplist(pack_index(Ip, Jp, Kk, KC), Tiles0, Tiles1),
   Ctx = Ctx1.put(stage, Tiles1),
   extent(PI, NI), extent(D, N),
   maplist(var_name(Ctx), [I, J, K], [CI, CJ, CK]),
   reverse(Batch, Rev), foldl(batch_id(Ctx), Rev, ''-(get_global_id(0) / Threads), BatchIds-_),
   phrase(( fmt("  int t = get_global_id(0) % ~d;\n~w", [Threads, BatchIds]),
            sequence(panel(KC, MCT, NSC), Tiles1),
            privates(Ctx),
            fmt("  for (int jc = 0; jc < ~d; jc += ~d) {\n", [NS, NSC]),
            fmt("  for (int kb = 0; kb < ~d; kb += ~d) {\n", [N, KC]),
            sequence(pack_panel(Ctx, I-Mb-Ip-Ii1, J-(T*NS + Jc)-Jp-Jj1, K-Kb-Kk, KC, MCT, NSC, outer), Tiles1),
            fmt("  for (int mb = 0; mb < ~d; mb += ~d) {\n", [NI, MCT]),
            sequence(pack_panel(Ctx, I-Mb-Ip-Ii1, J-(T*NS + Jc)-Jp-Jj1, K-Kb-Kk, KC, MCT, NSC, inner), Tiles1),
            fmt("  for (int jp = 0; jp < ~d; jp++) {\n  int ~w = t * ~d + jc + jp;\n", [NSC, CJ, NS]),
            fmt("  for (int ip = 0; ip < ~d; ip++) {\n  int ~w = mb + ip;\n", [MCT, CI]),
            prologue(Ctx, copy_in), pre(Ctx, Tiles),
            fmt("  #pragma unroll 8\n  for (int k = 0; k < ~d; k++) {\n  int ~w = kb + k;\n", [KC, CK]),
            loops(Ctx, Tiles, Eqs),
            "  }\n",
            post(Ctx, Tiles), prologue(Ctx, copy_out),
            "  }\n  }\n  }\n  }\n  }\n" ), Codes).

% group_ids(+Ctx, +Batch, +I, +J, +G, +GI, +GJ, -C): the group's position in the grid of
% groups: a batch point, then the strips, whole, or ranged, with start and count in strips.
group_ids(Ctx, Batch, I, J, G, GI, GJ, C) :-
   get_dict(ranges, Ctx, Ranges),
   group_axis(Ctx, Ranges, J, G, GJ, StartJ, CountJ),
   group_axis(Ctx, Ranges, I, G, GI, StartI, CountI),
   format(atom(C0), "  int gi = ~w + (g / ~w) % ~w;\n  int gj = ~w + g % ~w;\n", [StartI, CountJ, CountI, StartJ, CountJ]),
   reverse(Batch, Rev), foldl(batch_id(Ctx), Rev, C0-(g / (CountI*CountJ)), C-_).

% batch_id(+Ctx, +Axis, +C0-Rest0, -C-Rest): the last batch axis takes Rest0 modulo its
% extent, the earlier ones the quotient.
batch_id(Ctx, B:E, C0-Rest0, C-Rest) :-
   count(Ctx, E, N), var_name(Ctx, B, Name),
   format(atom(C), "~w  int ~w = (~w) % ~w;\n", [C0, Name, Rest0, N]),
   Rest = (Rest0 / N).

group_axis(Ctx, Ranges, I, G, _, Start, Count), member(I1-range(_, _), Ranges), I1 == I =>
   var_name(Ctx, I, Name),
   format(atom(Start), "(lo_~w / ~d)", [Name, G]), format(atom(Count), "(n_~w / ~d)", [Name, G]).
group_axis(_, _, _, _, GJ, Start, Count) =>
   Start = 0, Count = GJ.

unroll_pragma(TK, Pragma), TK =< 16 => Pragma = '#pragma unroll'.
unroll_pragma(_, Pragma) => Pragma = '#pragma unroll 8'.

pragma_of(E, Pragma), ground(E) => extent(E, N), unroll_pragma(N, Pragma).
pragma_of(_, Pragma) => Pragma = '#pragma unroll 8'.

% pack_index(+Ip, +Jp, +Kk, +KC, +Tile0, -Tile): the element of a panel the micro-kernel reads.
pack_index(Ip, _, Kk, KC, tile(R, A, Ii, T, k_last, Name), Tile), A \== none =>
   Tile = tile(R, A, Ii, T, k_last, Name, (Ip*KC + Kk)*T + Ii).
pack_index(_, Jp, Kk, KC, tile(R, A, Jj, T, k_first, Name), Tile) =>
   Tile = tile(R, A, Jj, T, k_first, Name, (Jp*KC + Kk)*T + Jj).
pack_index(_, _, Kk, _, tile(R, none, none, T, M, Name), Tile) =>
   Tile = tile(R, none, none, T, M, Name, Kk).

panel(KC, MCT, NS, tile(R, _, _, T, Major, Name, _)) -->
   { panel_tiles(Major, MCT, NS, Count), Size is Count*T*KC, tile_type(R, CT) },
   local_array(CT, Name, Size).

panel_tiles(k_last, MCT, _, Count) => Count = MCT.
panel_tiles(k_first, _, NS, Count) => Count = NS.

% pack_panel: the loops filling a panel from its read, at the outer level for the reads of the
% second strip, the slice of the thread, at the inner level for those of the first strip, the
% block of rows, and K-only reads with the outer ones.
pack_panel(Ctx, I-Mb-Ip-Ii1, _, K-Kb-Kk, KC, MCT, _, inner, tile(R, A, Ii, T, k_last, Name, _)) -->
   { A == I }, !,
   { core:place(R, N, Subs), subst([I-(Mb + Ip), Ii-Ii1, K-(Kb + Kk)], Subs, Subs1), global(Ctx, N, Subs1, Element),
     index(Ctx, (Ip*KC + Kk)*T + Ii1, Idx), pack_order(Ctx, N, Subs, K, k-KC, ii-T, Inner, Outer) },
   fmt("  for (int ip = 0; ip < ~d; ip++) ~w ~w ~w[~w] = ~w;\n", [MCT, Outer, Inner, Name, Idx, Element]).
pack_panel(Ctx, _, J-Start-Jp-Jj1, K-Kb-Kk, KC, _, NS, outer, tile(R, A, Jj, T, k_first, Name, _)) -->
   { A == J }, !,
   { core:place(R, N, Subs), subst([J-(Start + Jp), Jj-Jj1, K-(Kb + Kk)], Subs, Subs1), global(Ctx, N, Subs1, Element),
     index(Ctx, (Jp*KC + Kk)*T + Jj1, Idx), pack_order(Ctx, N, Subs, K, k-KC, jj-T, Inner, Outer) },
   fmt("  for (int jp = 0; jp < ~d; jp++) ~w ~w ~w[~w] = ~w;\n", [NS, Outer, Inner, Name, Idx, Element]).
pack_panel(Ctx, _, _, K-Kb-Kk, KC, _, _, outer, tile(R, A, _, _, _, Name, _)) -->
   { A == none }, !,
   { core:place(R, N, Subs), subst([K-(Kb + Kk)], Subs, Subs1), global(Ctx, N, Subs1, Element) },
   fmt("  for (int k = 0; k < ~d; k++) ~w[k] = ~w;\n", [KC, Name, Element]).
pack_panel(_, _, _, _, _, _, _, _, _) --> [].

% pack_order(+Ctx, +N, +Subs, +K, +k-KC, +s-T, -Inner, -Outer): the two loops filling a panel
% from the read of N at Subs, the inner one along the axis the read is contiguous in, K or
% the strip, so that the global reads run along cache lines.
pack_order(Ctx, N, Subs, K, KLoop, SLoop, Inner, Outer) :-
   access(Ctx, N, Subs, _-Off),
   ( stride(K, Off, 1) -> In = KLoop, Out = SLoop ; In = SLoop, Out = KLoop ),
   loop_header(In, Inner), loop_header(Out, Outer).

loop_header(V-E, C) :- format(atom(C), "for (int ~w = 0; ~w < ~d; ~w++)", [V, V, E, V]).

% fresh(+Ctx0, +Pairs, -Ctx): Ctx0 with the variables of Pairs named as given.
fresh(Ctx0, Pairs, Ctx) :-
   get_dict(env, Ctx0, Env0),
   append(Pairs, Env0, Env),
   Ctx = Ctx0.put(env, Env).

% tile_index(+I-Li, +J-Lj, +Kk, +TK, +G, +Tile0, -Tile): the element of the tile a work item
% reads: its local index times the width plus the tile loop index, and kk, in the layout.
tile_index(_, _, Kk, _, _, tile(R, none, none, T, M, Name), Tile) =>
   Tile = tile(R, none, none, T, M, Name, Kk).
tile_index(I-Li, J-Lj, Kk, TK, G, tile(R, A, S, T, M, Name), Tile) =>
   local_of(A, I, J, Li, Lj, L),
   layout(M, L, S, T, TK, G, Kk, Index),
   Tile = tile(R, A, S, T, M, Name, Index).

local_of(A, I, _, Li, _, L), A == I => L = Li.
local_of(_, _, _, _, Lj, L) => L = Lj.

layout(k_last, L, S, T, TK, _, Kk, Index) => Index = (L*T + S)*TK + Kk.
layout(k_first, L, S, T, _, G, Kk, Index) => Width is G*T, Index = Kk*Width + (L*T + S).

local_tile(G, TK, tile(R, A, _, T, _, Name, _)) -->
   { tile_rows(A, G, T, Rows), Size is Rows*TK, tile_type(R, CT) },
   local_array(CT, Name, Size).

tile_rows(none, _, _, Rows) => Rows = 1.
tile_rows(_, G, T, Rows) => Rows is G*T.

group_of(Axis, I, _, Gi, _, GP), Axis == I => GP = Gi.
group_of(Axis, _, J, _, Gj, GP), Axis == J => GP = Gj.
group_of(_, _, _, _, _, GP) => GP = none.



% kernel_text(+I, +Ctx, +Names, +Codes, -Source): the kernel k<I>: a pointer and an element
% offset per name, the name's buffer and its place in it, the pointer moved to the place first.
kernel_text(I, Ctx, Names, Codes, Source) :-
   maplist(param(Ctx), Names, Params0),
   get_dict(free, Ctx, Free),
   maplist(index_param(Ctx), Free, Params1),
   get_dict(ranges, Ctx, Ranges),
   maplist(range_params(Ctx), Ranges, Params2),
   get_dict(extents, Ctx, Extents),
   maplist(index_param(Ctx), Extents, Params3),
   append([Params0, Params1, Params2, Params3], Params),
   atomic_list_concat(Params, ", ", ParamList),
   maplist(offset_prologue(Ctx), Names, Prologue0),
   atomic_list_concat(Prologue0, Prologue),
   string_codes(Body, Codes),
   format(string(Source), "__kernel void k~d(~w) {~n~w~w}~n~n", [I, ParamList, Prologue, Body]).

offset_prologue(Ctx, N, Line) :-
   var_name(Ctx, N, Name),
   format(atom(Line), "  ~w += o_~w;~n", [Name, Name]).

index_param(Ctx, V, Param) :-
   var_name(Ctx, V, Name),
   format(atom(Param), "int ~w", [Name]).

range_params(Ctx, I-range(_, _), Param) :-
   var_name(Ctx, I, Name),
   format(atom(Param), "int lo_~w, int n_~w", [Name, Name]).

param(Ctx, N, Param) :-
   var_name(Ctx, N, Name), ctype(N, T),
   format(atom(Param), "__global ~w *~w, int o_~w", [T, Name, Name]).

% A kernel of work-groups: a group per point of the rows, its items l of L sharing lm; or a
% work item per point, the only item of its row.
work_groups(Ctx, Rows, item) -->
   !,
   "  int l = 0;\n",
   group_rows(Ctx, Rows, "get_global_id(0)").
work_groups(Ctx, Rows, L) -->
   fmt("  int l = get_local_id(0);\n  __local float lm[~d];\n  __local int lmi[~d];\n", [L, L]),
   group_rows(Ctx, Rows, "get_group_id(0)").

group_rows(_, [], _) --> !.
group_rows(Ctx, Rows, Id) -->
   fmt("  int g = ~w;\n", [Id]),
   { reverse(Rows, Rev) },
   unravel(Ctx, Rev, "g").

% phase_code(+Ctx, +L, +Phase): a serial phase runs on item 0; a reduction accumulates each
% item's share of the axis in a register, folds the registers in lm as a tree, and item 0
% folds the result into the place; a spread phase gives each item a stride of the axis.
% A fence ends each phase, so the next one reads what it wrote.
phase_code(Ctx, _, serial(Eqs)) -->
   "  if (l == 0) {\n",
   sequence(statement(Ctx), Eqs),
   "  }\n",
   fence(Ctx).
phase_code(Ctx, L, reduce(K:D, Reds)) -->
   { var_name(Ctx, K, Name), count(Ctx, D, N) },
   sequence(register(Ctx), Reds),
   fmt("  for (int ~w = l; ~w < ~w; ~w += ~d) {\n", [Name, Name, N, Name, L]),
   sequence(accumulate(Ctx), Reds),
   "  }\n",
   sequence(combine(Ctx, L), Reds).
phase_code(Ctx, L, spread(Axes, Ranges, Eqs)) -->
   { maplist(spread_axis(Ctx, Ranges), Axes, Counts, Starts),
     atomic_list_concat(Counts, " * ", Product) },
   "  {\n",
   fmt("  for (int v = l; v < ~w; v += ~d) {\n", [Product, L]),
   unravel_spread(Ctx, Axes, Counts, Starts, "v"),
   sequence(statement(Ctx), Eqs),
   "  }\n  }\n",
   fence(Ctx).
phase_code(Ctx, L, loop(T, E, Phases)) -->
   { var_name(Ctx, T, Name), count(Ctx, E, N) },
   fmt("  for (int ~w = 0; ~w < ~w; ~w++) {\n", [Name, Name, N, Name]),
   sequence(phase_code(Ctx, L), Phases),
   "  }\n".

% spread_axis(+Ctx, +Ranges, +Axis, -Count, -Start): the items of a spread axis, as C, from
% its guard range when it has one, 0 items at least.
spread_axis(Ctx, Ranges, I:_, Count, Start), member(I1-range(Lo, N), Ranges), I1 == I =>
   index(Ctx, Lo, Start), index(Ctx, N, CN), format(atom(Count), "max(~w, 0)", [CN]).
spread_axis(Ctx, _, _:E, Count, Start) =>
   count(Ctx, E, Count), Start = 0.

unravel_spread(_, [], _, _, _) --> [].
unravel_spread(Ctx, [I:_ | Axes], [Count | Counts], [Start | Starts], V) -->
   { var_name(Ctx, I, Name) },
   fmt("  int ~w = ~w + ~w % ~w;\n", [Name, Start, V, Count]),
   { format(string(V1), "(~w / ~w)", [V, Count]) },
   unravel_spread(Ctx, Axes, Counts, Starts, V1).

register(Ctx, red(G, _, Op, _)) -->
   { var_name(Ctx, G, Name), ctype(G, T), identity(Op, T, Identity), value(Ctx, Identity, CI) },
   fmt("  ~w p_~w = ~w;\n", [T, Name, CI]).

accumulate(Ctx, red(G, _, Op, E)) -->
   { var_name(Ctx, G, Name), ctype(G, T), format(atom(P), "p_~w", [Name]), value(Ctx, E, CE), fold(Op, T, P, CE, C) },
   fmt("  ~w = ~w;\n", [P, C]).

combine(Ctx, 1, red(G, Ts, Op, _)) -->
   !,
   { var_name(Ctx, G, Name), ctype(G, T), place(Ctx, G, Ts, Place), format(atom(P), "p_~w", [Name]), fold(Op, T, Place, P, Final) },
   fmt("  ~w = ~w;\n", [Place, Final]).
combine(Ctx, L, red(G, Ts, Op, _)) -->
   { var_name(Ctx, G, Name), ctype(G, T), scratch(T, Lm), place(Ctx, G, Ts, Place), Half is L // 2,
     format(atom(Lhs), "~w[l]", [Lm]), format(atom(Rhs), "~w[l + s]", [Lm]), format(atom(Top), "~w[0]", [Lm]),
     fold(Op, T, Lhs, Rhs, Tree), fold(Op, T, Place, Top, Final) },
   fmt("  ~w[l] = p_~w;\n  barrier(CLK_LOCAL_MEM_FENCE);\n", [Lm, Name]),
   fmt("  for (int s = ~d; s > 0; s >>= 1) { if (l < s) ~w[l] = ~w; barrier(CLK_LOCAL_MEM_FENCE); }\n",
       [Half, Lm, Tree]),
   fmt("  if (l == 0) ~w = ~w;\n", [Place, Final]),
   fence(Ctx).

fence --> "  barrier(CLK_GLOBAL_MEM_FENCE | CLK_LOCAL_MEM_FENCE);\n".

fence(Ctx) --> { get_dict(items, Ctx, 1) }, !, [].
fence(Ctx) --> { get_dict(fence, Ctx, local) }, !, "  barrier(CLK_LOCAL_MEM_FENCE);\n".
fence(_) --> fence.

% fold(+Op, +T, +A, +B, -C): the fold of A and B by Op in the C type T.
fold(Op, _, A, B, C), memberchk(Op, [+, *]) => format(atom(C), "(~w ~w ~w)", [A, Op, B]).
fold(Op, float, A, B, C) => format(atom(C), "f~w(~w, ~w)", [Op, A, B]).
fold(Op, _, A, B, C) => format(atom(C), "~w(~w, ~w)", [Op, A, B]).

% scratch(+T, -Lm): the local array of the reduction tree of the C type T.
scratch(float, Lm) => Lm = lm.
scratch(int, Lm) => Lm = lmi.

var_name(Ctx, V, Name) :-
   get_dict(env, Ctx, Env),
   member(V1-Name, Env),
   V1 == V,
   !.

% A kernel is enqueued over one dimension: the work item unravels its id into the parallel
% axes, a ranged one from the count and the start its parameters give.
work_items(_, []) --> !.
work_items(Ctx, Par) -->
   "  size_t g = get_global_id(0);\n",
   { reverse(Par, Rev) },
   unravel(Ctx, Rev, "g").

unravel(_, [], _) --> [].
unravel(Ctx, [I:E | Par], G) -->
   { var_name(Ctx, I, Name), count_of(Ctx, I, E, Name, Count, Start) },
   fmt("  int ~w = ~w + ~w % ~w;\n", [Name, Start, G, Count]),
   { format(string(G1), "(~w / ~w)", [G, Count]) },
   unravel(Ctx, Par, G1).

count_of(Ctx, I, _, Name, Count, Start), get_dict(ranges, Ctx, Ranges), member(I1-range(_, _), Ranges), I1 == I =>
   format(atom(Count), "n_~w", [Name]), format(atom(Start), "lo_~w", [Name]).
count_of(Ctx, _, E, _, Count, Start) =>
   count(Ctx, E, Count), Start = 0.

privates(Ctx) -->
   { get_dict(local, Ctx, Local), get_dict(priv, Ctx, Priv) },
   sequence(private_local(Ctx), Local),
   sequence(private_tile(Ctx), Priv).

private_local(Ctx, N) -->
   { private_extents(Ctx, N, Es), private_size(Es, Size), var_name(Ctx, N, Name), ctype(N, T) },
   fmt("  ~w p_~w[~d] = {0};\n", [T, Name, Size]).   % pocl 7.1 breaks an uninitialised array

private_tile(Ctx, N-Infos) -->
   { maplist(info_width, Infos, Es), private_size(Es, Size), var_name(Ctx, N, Name), ctype(N, T) },
   fmt("  ~w r_~w[~d] = {0};\n", [T, Name, Size]).

size(Es, Size) :-
   foldl(times, Es, 1, Size).

times(E, S0, S) :-
   extent(E, N),
   S is S0*N.

% count(+Ctx, +E, -C): the extent E as C: its value, or its expression in the kernel's int
% parameters while unknown.
count(_, E, C), ground(E) => C is E.
count(Ctx, E, C) => index(Ctx, E, C).

% extent_term(+E, -T): the extent E folded to its value when known, else itself, for a term.
extent_term(E, T), ground(E) => T is E.
extent_term(E, T) => T = E.

% extent_max(+E, -N): the most the extent E can be; fails while it has no upper bound.
extent_max(E, N), ground(E) => N is E.
extent_max(E, N) =>
   term_variables(E, Vs),
   maplist(upper_bound, Vs, His),
   pairs_keys_values(Pairs, Vs, His),
   subst(Pairs, E, E1),
   N is E1.

upper_bound(V, Hi) :-
   range(V, [_, Hi]),
   Hi < inf.

% size_max(+Es, -Size): the most elements the extents Es span; fails while one has no upper
% bound. private_size/2 is the same for an array a kernel declares, which must have one.
size_max(Es, Size) :-
   foldl(times_max, Es, 1, Size).

times_max(E, S0, S) :-
   extent_max(E, N),
   S is S0*N.

private_size(Es, Size) :-
   (  size_max(Es, Size)
   -> true
   ;  existence_error(upper_bound, Es)
   ).

% extent(+E, -N): the value of the extent E, the least one while it is unknown.
extent(E, N), ground(E) => N is E.
extent(E, N) =>
   term_variables(E, Vs),
   maplist(lower, Vs, Los),
   pairs_keys_values(Pairs, Vs, Los),
   subst(Pairs, E, E1),
   N is E1.

lower(V, Lo) :-
   range(V, [Lo, _]).

% prologue(+Ctx, +Way): a private name is read from its buffer before the loops and written
% back after them, by loops over its tile axes.
prologue(Ctx, Way) -->
   { get_dict(priv, Ctx, Priv), get_dict(temps, Ctx, Temps), get_dict(inits, Ctx, Inits),
     skipped(Way, Temps, Inits, Skipped),
     exclude(temp_of(Skipped), Priv, Copied) },
   sequence(copy(Ctx, Way), Copied).

skipped(copy_in, Temps, Inits, Skipped) => append(Temps, Inits, Skipped).
skipped(copy_out, Temps, _, Skipped) => Skipped = Temps.

temp_of(Temps, N-_) :-
   in_list(Temps, N).

% The initialisation before the loops and the elementwise epilogue after them.
pre(Ctx, Tiles) --> { get_dict(pre, Ctx, Pre) }, loops(Ctx, Tiles, Pre).
post(Ctx, Tiles) --> { get_dict(post, Ctx, Post) }, loops(Ctx, Tiles, Post).

copy(Ctx, Way, N-Infos) -->
   { get_dict(box, Ctx, Box), get_dict(pre, Ctx, Pre), get_dict(post, Ctx, Post),
     accesses(Box-Pre-Post, N, [S | _]), maplist(info_axis, Infos, Axes) },
   loops(Ctx, Axes, [copy(Way, N, S)]).

% loops(+Ctx, +Axes, +Eqs): the loop nest of Axes around the statements Eqs. A last loop of the
% vector width whose statements all read and write along it contiguously, or not at all, is
% one vector statement each.
loops(Ctx, [], Eqs) --> sequence(statement(Ctx), Eqs).
loops(Ctx, Axes, [P := V]) -->
   { Axes = [_ | _], register_fold(Axes, P, V, N, Ts, Op, X), !,
     access(Ctx, N, Ts, Access), load(Ctx, Access, R0), ctype(N, T), var_name(Ctx, N, Name),
     format(atom(Reg), "a_~w", [Name]), store(Ctx, Access, Reg, Store) },
   fmt("  { ~w ~w = ~w;\n", [T, Reg, R0]),
   loops(Ctx, Axes, [fold(Reg, T, Op, X)]),
   fmt("  ~w }\n", [Store]).
loops(Ctx, [V:E], Eqs) -->
   { get_dict(vector, Ctx, W), W > 1, ground(E), extent(E, N), N mod W =:= 0, vectorizable(Ctx, V, Eqs),
     Vec = Ctx.put(vec, V), Last is N - W, numlist(0, Last, Offs), include([O]>>(O mod W =:= 0), Offs, Starts) },
   !,
   sequence(vector_chunk(Vec, V, Eqs), Starts).
loops(Ctx, [I:E | Axes], Eqs) -->
   { get_dict(unroll, Ctx, Unroll), in_list(Unroll, I), ground(E), extent(E, N), N =< 16, Last is N - 1, numlist(0, Last, Vs) },
   !,
   sequence(unrolled(Ctx, I, Axes, Eqs), Vs).
loops(Ctx, [I:E | Axes], Eqs) -->
   { var_name(Ctx, I, Name), count(Ctx, E, N), pragma_of(E, Pragma) },
   fmt("  ~w\n  for (int ~w = 0; ~w < ~w; ~w++) {\n", [Pragma, Name, Name, N, Name]),
   loops(Ctx, Axes, Eqs),
   "  }\n".

% register_fold(+Axes, +P, +V, -N, -Ts, -Op, -X): the one equation of a loop nest over Axes
% folds the place P = N[Ts] by the monoid Op with X, the place free of the loop indices and X
% not reading N: the loops accumulate in a register, the place loaded before and stored after.
register_fold(Axes, P, V, N, Ts, Op, X) :-
   core:place(P, N, Ts),
   V =.. [Op, R, X],
   monoid(Op, _),
   core:place(R, N1, Ts1), N1 == N, Ts1 == Ts,
   maplist(arg(1), Axes, Is),
   \+ ( member(I, Is), mentions(Ts, I) ),
   names(X, Ns),
   \+ in_list(Ns, N).

% A chunk of the vector loop starts at Off: the lane index is V + Off.
vector_chunk(Vec, V, Eqs, Off) -->
   { rename([V-(V+Off)], Vec, Eqs, Vec1, Eqs1) },
   sequence(statement(Vec1), Eqs1).

% An unrolled loop: the body once per value of the index, as a constant.
unrolled(Ctx, I, Axes, Eqs, X) -->
   { rename([I-X], Ctx, Eqs, Ctx1, Eqs1) },
   loops(Ctx1, Axes, Eqs1).

% rename(+Pairs, +Ctx0, +Eqs0, -Ctx, -Eqs): the substitution applied to the statements and to
% the staged reads they are matched against.
rename(Pairs, Ctx0, Eqs0, Ctx, Eqs) :-
   subst(Pairs, Eqs0, Eqs),
   get_dict(stage, Ctx0, Tiles0),
   maplist(subst_tile(Pairs), Tiles0, Tiles),
   Ctx = Ctx0.put(stage, Tiles).

subst_tile(Pairs, tile(R0, A, S, T, M, Name, Index0), tile(R, A, S, T, M, Name, Index)) :-
   subst(Pairs, R0, R),
   subst(Pairs, Index0, Index).

% vectorizable(+Ctx, +V, +Eqs): every statement writes a place contiguous along V and computes
% it with elementwise arithmetic whose reads are contiguous along V or free of it.
vectorizable(Ctx, V, Eqs) :-
   forall(member(Eq, Eqs), vectorizable_eq(Ctx, V, Eq)).

vectorizable_eq(Ctx, V, P := Val) :-
   core:place(P, N, Ts),
   get_dict(atomics, Ctx, Atomics), \+ ( member(N1-_, Atomics), N1 == N ),
   access(Ctx, N, Ts, _-Off),
   stride(V, Off, 1),
   lanes(Ctx, V, Val).
vectorizable_eq(Ctx, V, copy(_, N, S)) :-
   access(Ctx, N, S, _-Off), stride(V, Off, 1),
   global_access(Ctx, N, S, _-GOff), stride(V, GOff, 1).

% lanes(+Ctx, +V, +Val): Val is elementwise, its reads contiguous along V or constant in it;
% the lane index V itself is the vector of lane numbers, and a comparison or a selection on
% it is lane-wise.
lanes(_, _, X), var(X), \+ is_name(X) => true.
lanes(Ctx, V, R), core:place(R, N, Ts) => access(Ctx, N, Ts, _-Off), stride(V, Off, S), memberchk(S, [0, 1]).
lanes(_, _, X), number(X) => true.
lanes(Ctx, V, E), E =.. [Op | As], memberchk(Op-_, [(+)-2, (-)-2, (*)-2, (/)-2, (-)-1, max-2, min-2, exp-1, sqrt-1, log-1,
                                                    (<)-2, (=<)-2, (=:=)-2, where-3]) =>
   maplist(lanes(Ctx, V), As).
lanes(_, _, _) => fail.

% stride(+V, +Off, -S): the coefficient of V in the affine offset Off.
stride(V, Off, S) :-
   term_variables(Off, Vs),
   maplist([X, X:1]>>true, Vs, Scope),
   catch(core:form(Scope, Off, 1, 0-[], _-Pairs), error(_, _), fail),
   \+ ( member(Key-_, Pairs), nonvar(Key) ),      % a remainder has no stride
   foldl(coef(V), Pairs, 0, S).

coef(V, X-K, S0, S), X == V => S is S0 + K.
coef(_, _, S0, S) => S = S0.

statement(Ctx, over(Axes, Eqs)) --> loops(Ctx, Axes, Eqs).
statement(Ctx, fold(Reg, T, Op, X)) -->
   { value(Ctx, X, CX), fold(Op, T, Reg, CX, C) },
   fmt("  ~w = ~w;\n", [Reg, C]).
statement(Ctx, copy(Way, N, S)) -->
   { access(Ctx, N, S, Private), global_access(Ctx, N, S, Global),
     way(Way, Global, Private, From, To), load(Ctx, From, R), store(Ctx, To, R, C) },
   fmt("  ~w\n", [C]).
statement(Ctx, P := V) -->
   { core:place(P, N, Ts), get_dict(atomics, Ctx, Atomics), member(N1-Op, Atomics), N1 == N, !,
     V =.. [Op, _, E], value(Ctx, E, R), access(Ctx, N, Ts, Name-Off), index(Ctx, Off, CO),
     ctype(N, T), atomic_function(Op, T, F) },
   fmt("  ~w(&~w[~w], ~w);\n", [F, Name, CO, R]).
statement(Ctx, P := V) -->
   { core:place(P, N, Ts), access(Ctx, N, Ts, Access), value(Ctx, V, R), store(Ctx, Access, R, C) },
   fmt("  ~w\n", [C]).

atomic_function(+, float, F) => F = atomic_add_float.
atomic_function(max, float, F) => F = atomic_max_float.
atomic_function(min, float, F) => F = atomic_min_float.
atomic_function(*, float, F) => F = atomic_mul_float.
atomic_function(+, int, F) => F = atomic_add.
atomic_function(max, int, F) => F = atomic_max.
atomic_function(min, int, F) => F = atomic_min.
atomic_function(*, int, F) => F = atomic_mul_int.

% access(+Ctx, +N, +Ts, -Name-Off): the C array holding N[Ts], private over its tiles, local or
% global, and the offset in it, a term.
access(Ctx, N, Ts, Access), get_dict(priv, Ctx, Priv), member(N1-Infos, Priv), N1 == N =>
   var_name(Ctx, N, Name), maplist(coordinate(Ts), Infos, Cs), maplist(info_width, Infos, Es),
   offset(Cs, Es, Off), format(atom(Private), "r_~w", [Name]), Access = Private-Off.

access(Ctx, N, Ts, Access), get_dict(local, Ctx, Local), in_list(Local, N) =>
   var_name(Ctx, N, Name), private_extents(Ctx, N, Es), private_coords(Ctx, Ts, Cs), offset(Cs, Es, Off),
   format(atom(Private), "p_~w", [Name]), Access = Private-Off.
access(Ctx, N, Ts, Access), get_dict(shared, Ctx, Shared), member(N1-Drop-_, Shared), N1 == N =>
   var_name(Ctx, N, Name), shape(N, Shape),
   length(P, Drop), append(P, Rest, Shape), length(P1, Drop), append(P1, Ts1, Ts),
   offset(Ts1, Rest, Off), format(atom(Local), "s_~w", [Name]), Access = Local-Off.
access(Ctx, N, Ts, Access) =>
   var_name(Ctx, N, Name), shape(N, Shape), offset(Ts, Shape, Off), Access = Name-Off.
% coordinate(+Ts, +Info, -C): the tile coordinate of the place: its subscript at the tile's
% position with every other index at 0, the work item's strip and any batch offset, which
% a compiler folds to the loop index.
coordinate(Ts, info(Ii, _, P, _), C) :-
   nth0(P, Ts, Sp),
   term_variables(Sp, Vs), exclude(==(Ii), Vs, Others),
   maplist([V, V-0]>>true, Others, Pairs),
   subst(Pairs, Sp, C).


% load(+Ctx, +Access, -C) and store(+Ctx, +Access, +Value, -C): a read and a write of the
% element, or of the vector along the lane of Ctx when the offset moves with it.
load(Ctx, Name-Off, C), get_dict(vec, Ctx, V), V \== none, stride(V, Off, 1) =>
   subst([V-0], Off, Off0), index(Ctx, Off0, CO), get_dict(vector, Ctx, W),
   lanes_read(W, Name, CO, C).
load(Ctx, Name-Off, C) =>
   index(Ctx, Off, CO), format(atom(C), "~w[~w]", [Name, CO]).

store(Ctx, Name-Off, R, C), get_dict(vec, Ctx, V), V \== none =>
   subst([V-0], Off, Off0), index(Ctx, Off0, CO), get_dict(vector, Ctx, W),
   format(atom(Val), "(float~d)(~w)", [W, R]),
   vector_write(W, Name, CO, Val, C).
store(Ctx, Name-Off, R, C) =>
   index(Ctx, Off, CO), format(atom(C), "~w[~w] = ~w;", [Name, CO, R]).

place(Ctx, N, Ts, C) :-
   access(Ctx, N, Ts, Access),
   load(Ctx, Access, C).

global(Ctx, N, Ts, C) :-
   var_name(Ctx, N, Name), shape(N, Shape), offset(Ts, Shape, Off), index(Ctx, Off, CO),
   format(atom(C), "~w[~w]", [Name, CO]).

global_access(Ctx, N, Ts, Name-Off) :-
   var_name(Ctx, N, Name), shape(N, Shape), offset(Ts, Shape, Off).

way(copy_in, Global, Private, From, To) => From = Global, To = Private.
way(copy_out, Global, Private, From, To) => From = Private, To = Global.

% offset(+Ts, +Shape, -Off): the row-major offset of Ts in Shape, a term.
offset(Ts, Shape, Off) :-
   foldl([T, E, Off0, (Off0*N + T)]>>extent_term(E, N), Ts, Shape, 0, Off).

% index(+Ctx, +E, -C) and value(+Ctx, +E, -C): E as a C int, or a C float.
index(Ctx, V, C), var(V) => var_name(Ctx, V, C).
index(_, N, C), integer(N) => C = N.
index(Ctx, R, C), core:place(R, N, Ts) => place(Ctx, N, Ts, P), format(atom(C), "(int)~w", [P]).
index(Ctx, E, C), E =.. [Op, A, B], c_int_op(Op, COp) =>
   index(Ctx, A, CA), index(Ctx, B, CB), format(atom(C), "(~w ~w ~w)", [CA, COp, CB]).
index(Ctx, where(I, T, E), C) =>
   value(Ctx, I, CI), index(Ctx, T, CT), index(Ctx, E, CE), format(atom(C), "(~w ? ~w : ~w)", [CI, CT, CE]).
index(Ctx, E, C), E =.. [F, A, B], memberchk(F, [max, min]) =>
   index(Ctx, A, CA), index(Ctx, B, CB), format(atom(C), "~w(~w, ~w)", [F, CA, CB]).
index(_, E, _) => type_error(index_expression, E).

value(Ctx, V, C), var(V), is_name(V) => place(Ctx, V, [], C).
value(Ctx, V, C), var(V), get_dict(vec, Ctx, L), L == V =>
   get_dict(vector, Ctx, W), Last is W-1, numlist(0, Last, Ns), atomic_list_concat(Ns, ',', Lanes),
   format(atom(C), "((int~d)(~w))", [W, Lanes]).
value(Ctx, V, C), var(V) => var_name(Ctx, V, C).
value(_, N, C), integer(N) => C = N.
value(_, N, C), number(N), N =:= inf => C = 'INFINITY'.
value(_, N, C), number(N), N =:= -inf => C = '-INFINITY'.
value(_, N, C), number(N) => F is float(N), format(atom(C), "~wf", [F]).
value(Ctx, R, C), get_dict(stage, Ctx, Tiles), member(tile(R1, _, _, _, _, Name, Index), Tiles), R1 == R =>
   load(Ctx, Name-Index, C).
value(Ctx, R, C), core:place(R, N, Ts) => place(Ctx, N, Ts, C).
value(Ctx, where(I, T, E), C), get_dict(vec, Ctx, L), L \== none =>
   get_dict(vector, Ctx, W), maplist(value(Ctx), [I, T, E], [CI, CT, CE]),
   format(atom(C), "(~w ? (float~d)(~w) : (float~d)(~w))", [CI, W, CT, W, CE]).
value(Ctx, where(I, T, E), C) =>
   maplist(value(Ctx), [I, T, E], [CI, CT, CE]), format(atom(C), "(~w ? ~w : ~w)", [CI, CT, CE]).
value(Ctx, A*B + X, C), has_read(A*B), kind_of(A*B + X, 2) =>
   maplist(value(Ctx), [A, B, X], [CA, CB, CX]), format(atom(C), "fma(~w, ~w, ~w)", [CA, CB, CX]).
value(Ctx, X + A*B, C), has_read(A*B), kind_of(X + A*B, 2) =>
   maplist(value(Ctx), [A, B, X], [CA, CB, CX]), format(atom(C), "fma(~w, ~w, ~w)", [CA, CB, CX]).
value(Ctx, E, C), E =.. [Op, A, B], memberchk(Op, [+, -, *, <, =<, =:=]) =>
   maplist(value(Ctx), [A, B], [CA, CB]), c_op(Op, COp), format(atom(C), "(~w ~w ~w)", [CA, COp, CB]).
value(Ctx, E, C), E =.. [Op, A, B], c_int_op(Op, COp), core:int_op(Op) =>
   maplist(value(Ctx), [A, B], [CA, CB]), format(atom(C), "(~w ~w ~w)", [CA, COp, CB]).
value(Ctx, A / B, C) =>
   maplist(value(Ctx), [A, B], [CA, CB]), format(atom(C), "((float)~w / ~w)", [CA, CB]).
value(Ctx, -A, C) => value(Ctx, A, CA), format(atom(C), "(-~w)", [CA]).
value(Ctx, E, C), E =.. [F, A, B], memberchk(F, [max, min]) =>
   maplist(value(Ctx), [A, B], [CA, CB]), ( kind_of(E, 2) -> T = float ; T = int ), fold(F, T, CA, CB, C).
value(Ctx, E, C), E =.. [F, A], memberchk(F, [exp, sqrt, log]) =>
   value(Ctx, A, CA), format(atom(C), "~w(~w)", [F, CA]).
value(Ctx, bits(A), C) =>
   value(Ctx, A, CA), format(atom(C), "as_int((float)~w)", [CA]).

% has_read(+E): E reads a place, so fma applies when E is a float.
has_read(E) :-
   sub_term(T, E),
   core:place(T, N, _),
   is_name(N),
   !.

c_op(=<, C) => C = '<='.
c_op(=:=, C) => C = '=='.
c_op(Op, C) => C = Op.

% c_int_op(?Op, ?C): the C of an operation on ints; / and % agree with // and mod on the
% non-negative operands the bounds rule admits.
c_int_op(+, C) => C = (+).
c_int_op(-, C) => C = (-).
c_int_op(*, C) => C = (*).
c_int_op(//, C) => C = (/).
c_int_op(mod, C) => C = '%'.
c_int_op(>>, C) => C = (>>).
c_int_op(<<, C) => C = (<<).
c_int_op(/\, C) => C = (&).
c_int_op(\/, C) => C = '|'.
c_int_op(xor, C) => C = (^).
c_int_op(_, _) => fail.

fmt(Format, Args) --> { format(codes(Codes), Format, Args) }, Codes.

% Running
% =======

:- dynamic device_state/4, program_state/3.

% run(+Out, +Data, -Values, +Options): the elements of Out, row-major, computed on the device of
% device(Name), pocl by default, from Data, Name-List pairs, with the options of kernels/3,
% those not given derived from the device, and alloc(arena), the default, or alloc(separate),
% see allocate/8.

% device_options(+Device, -Options): the schedule parameters a device's properties call for.
%   vector  the native float vector of a CPU, its SIMD unit, whatever width its runtime
%           prefers to be handed; the preferred vector of a GPU, or 4 lanes on a scalar one,
%           for 16-byte loads;
%   major   the tile of the first strip K first where local memory is banked, so that the
%           items of a column read different banks, loaded by vectors along K stored
%           transposed; K last where it is a cache, so that each item sweeps K contiguously;
%   group   64 items per work-group, two warps, the least that fills a compute unit's
%           scheduler, fewer where the device allows fewer;
%   tile    rows of accumulators by two vectors: 8 rows on a GPU, whose register file holds
%           hundreds of values per item, 4 on a CPU, whose 16 vector registers hold 8 rows
%           of two vectors with nothing to spare; a step of K is then one broadcast per row,
%           2 vector loads and 2 vector fma per row on the register tile;
%   stage   the largest block of K, a power of two up to 64, whose two tiles take at most
%           a quarter of banked local memory, so that four groups share a compute unit, or
%           half the cache where local memory is the cache;
%   local   256 items for a reduction tree on a banked device, 64 on a cache, where a
%           barrier costs a loop split;
%   items   8 parallel points per compute unit, under which a reduction goes to groups;
%   threads on a CPU, one packing thread per compute unit; none on a GPU;
%   sweep   the items of a work-group running a sweep: a CPU runs it in one, whose phases
%           are plain loops without a barrier, a GPU in a group of local: one warp measured
%           slower, as a step's points outnumber it;
%   panel   the K block whose micro-panel of a vector pair stays in a 32 KB L1, and the row
%           block whose panel takes a quarter of the cache the runtime reports, capped at
%           256 and 128;
%   lanes   the items a work-group occupies at the least: the warp or wavefront of a GPU, the
%           vector of a CPU, whose runtime runs a group's items as lanes of one thread.
device_options(Device, [vector(W), major(Major), group(G), tile([TI, TJ]), stage(TK), local(L), items(Min),
                        threads(Threads), panel(KC, MC), lds(LocalBytes), sweep(SW), lanes(U)]) :-
   cl_device_info(Device, type, Type),
   rows(Type, TI),
   cl_device_info(Device, preferred_vector_width_float, PW),
   cl_device_info(Device, native_vector_width_float, NW),
   cl_device_info(Device, local_mem_type, LocalType),
   cl_device_info(Device, local_mem_size, LocalBytes),
   cl_device_info(Device, global_mem_cache_size, CacheBytes),
   cl_device_info(Device, max_work_group_size, MaxGroup),
   cl_device_info(Device, max_compute_units, CUs),
   lanes(Type, PW, NW, W),
   banked(LocalType, Major, Tree),
   G is min(8, 1 << (msb(MaxGroup) // 2)),
   TJ is 2*W,
   budget(LocalType, LocalBytes, CacheBytes, Budget),
   block_of(G, TI, TJ, Budget, TK),
   L is min(Tree, MaxGroup),
   Min is 8*CUs,
   threads(LocalType, CUs, Threads),
   sweep_items(LocalType, L, SW),
   KC is min(256, 16384 // (TJ*4)),
   MC is min(128, max(TI, CacheBytes // (4*KC*4))),
   group_lanes(LocalType, Device, L, W, U).

group_lanes(local, Device, L, _, U) => warp(Device, L, U).
group_lanes(global, _, _, W, U) => U = W.

sweep_items(global, _, SW) => SW = 1.
sweep_items(local, L, SW) => SW = L.

% warp(+Device, +L, -W): the warp or wavefront of the device, L when it does not say.
warp(Device, _, W), catch(cl_device_info(Device, warp_size, W0), _, fail) => W = W0.
warp(Device, _, W), catch(cl_device_info(Device, wavefront_width, W0), _, fail) => W = W0.
warp(_, L, W) => W = L.

threads(global, CUs, Threads) => Threads = CUs.
threads(local, _, Threads) => Threads = 0.

rows(gpu, TI) => TI = 8.
rows(_, TI) => TI = 4.

lanes(cpu, _, NW, W), NW > 1 => W is min(NW, 8).
lanes(_, PW, _, W), PW > 1 => W is min(PW, 8).
lanes(_, _, _, W) => W = 4.

banked(local, Major, Tree) => Major = k_first, Tree = 256.
banked(global, Major, Tree) => Major = k_last, Tree = 64.

budget(local, LocalBytes, _, Budget) => Budget is LocalBytes // 4.
budget(global, _, CacheBytes, Budget) => Budget is CacheBytes // 2.

% block_of(+G, +TI, +TJ, +Budget, -TK): the largest power of two block of K, at most 64,
% whose tiles of G*TI and G*TJ floats fit Budget bytes.
block_of(G, TI, TJ, Budget, TK) :-
   Rows is G*TI + G*TJ,
   aggregate_all(max(T), ( member(T, [2, 4, 8, 16, 32, 64]), Rows*T*4 =< Budget ), TK).
run(Out, Data, Values, Options0) :-
   option(device(DeviceName), Options0, pocl),
   device(DeviceName, Device, Context, Queue),
   device_options(Device, Derived),
   merge_options(Options0, Derived, Options),
   kernels(Out, Options, Plan),
   source(Plan, Source),
   built(Context, Device, Source, Program),
   findall(Vs, ( bind_extents(Plan, Data),
                 allocate(Context, Queue, Device, Plan, Out, Data, Options, Alloc),
                 get_dict(buffers, Alloc, Buffers),
                 run_plan(Queue, Program, Buffers, [], Plan),
                 cl_finish(Queue),
                 read_back(Queue, Buffers, Out, Vs) ),
           [Values]).

% bind_extents(+Term, +Data): the extents of the plan or boxes Term bound by the data: the
% length of each list given is the product of its name's shape, a relation clpBNR solves, and
% must leave the shape known; every other extent, of an output or an intermediate, takes the
% least value the program allows. Undone by the findall around the run, so that the program
% stays symbolic for the next.
bind_extents(Term, Data) :-
   maplist(bind_length, Data),
   maplist(given_known, Data),
   names(Term, Names),
   maplist(shape, Names, Shapes),
   term_variables(Term-Shapes, Vs),
   include(is_extent, Vs, Extents),
   maplist(least, Extents).

given_known(Name-_) :-
   shape(Name, Shape),
   (  term_variables(Shape, [V | _])
   -> existence_error(extent_value, V)
   ;  true
   ).

least(V) :-
   range(V, [Lo, _]),
   (  Lo < inf
   -> V = Lo
   ;  existence_error(extent_value, V)
   ).

bind_length(Name-List) :-
   length(List, Len),
   shape(Name, Shape),
   foldl([E, P0, P0*E]>>true, Shape, 1, P),
   (  {Len == P}
   -> true
   ;  domain_error(data_length(P), Name)
   ).

% run_plan(+Queue, +Program, +Buffers, +Env, +Plan): the kernels launched in order, a host
% loop's for each value of its index, Env holding the values of the indices around.
run_plan(Queue, Program, Buffers, Env, Plan) :-
   forall(member(Step, Plan), run_step(Queue, Program, Buffers, Env, Step)).

run_step(Queue, Program, Buffers, Env, loop(T, E, Inner)) =>
   extent(E, N), Last is N-1,
   forall(between(0, Last, V), run_plan(Queue, Program, Buffers, [T-V | Env], Inner)).
run_step(Queue, Program, Buffers, Env, Kernel) =>
   launch(Queue, Program, Buffers, Env, Kernel).

% device/4 and built/4 memoise under a mutex, so that tests may run concurrently; the
% queue is in order, so kernels and reads of different threads interleave safely.
device(Name, Device, Context, Queue) :-
   with_mutex(compile, device_(Name, Device, Context, Queue)).

device_(Name, Device, Context, Queue), device_state(Name, D, C, Q) =>
   Device = D, Context = C, Queue = Q.
device_(Name, Device, Context, Queue) =>
   opencl_device(Name, Device),
   cl_context(Device, Context),
   cl_queue(Context, Device, false, Queue),
   assertz(device_state(Name, Device, Context, Queue)).

built(Context, Device, Source, Program) :-
   with_mutex(compile, built_(Context, Device, Source, Program)).

built_(Context, _, Source, Program), program_state(Context, Source, P) => Program = P.
built_(Context, Device, Source, Program) =>
   cl_program(Context, Device, Source, "", Program),
   assertz(program_state(Context, Source, Program)).

% device_buffer(+Context, +Queue, +Data, +Name, -Mem): a buffer of Name, of its kind, holding
% its data when given, zeroes otherwise.
device_buffer(Context, Queue, Data, Name, Mem) :-
   shape(Name, Shape), size(Shape, N), Bytes is 4*max(N, 1),
   cl_buffer(Context, Bytes, Mem),
   (  member(Name1-List, Data), Name1 == Name
   -> ctype(Name, T), host_type(T, HT), maplist(coerce(T), List, Elements),
      Term =.. [data | Elements],
      buffer_from_data(Host, HT, N, Term),
      buffer_offset(Host, HT, N, 0, Pointer),
      cl_write(Queue, Mem, 0, Pointer, Bytes)
   ;  cl_fill(Queue, Mem, Bytes, [], Event),
      cl_wait([Event])
   ).

% coerce(+T, +X, -V): the number X as an element of the C type T.
coerce(float, X, V) => V is float(X).
coerce(int, X, V) => V is truncate(X).

% host_type(+T, -HT): the host buffer type of the C type T.
host_type(float, HT) => HT = float32.
host_type(int, HT) => HT = int32.

launch(Queue, Program, Buffers, Env, Kernel) :-
   kernel{id: I, names: Names, free: Free} :< Kernel,
   ranges_of(Kernel, Ranges),
   maplist(range_values(Env), Ranges, Values),
   (  member(_-(_, Count), Values), Count =< 0
   -> true                                            % nothing active at this step
   ;  format(atom(KName), "k~d", [I]),
      cl_kernel(Program, KName, K),
      foldl(buffer_args(Buffers), Names, [], Args0),
      maplist(index_arg(Env), Free, Args1),
      foldl([_-(Lo, Count), A0, A]>>append(A0, [int(Lo), int(Count)], A), Values, [], Args2),
      get_dict(extents, Kernel, Extents),
      maplist(extent_arg, Extents, Args3),
      append([Args0, Args1, Args2, Args3], Args),
      work(Kernel, Values, Global, Local),
      cl_enqueue(Queue, K, Args, Global, Local, [], _)
   ).

ranges_of(Kernel, Ranges), get_dict(ranges, Kernel, R) => Ranges = R.
ranges_of(_, Ranges) => Ranges = [].

range_values(Env, I-range(Lo, Count), I-(LoV, CountV)) :-
   value_in(Env, Lo, LoV),
   value_in(Env, Count, CountV).

value_in(Env, T, V) :-
   subst(Env, T, T1),
   V is T1.

index_arg(Env, V, int(X)) :-
   member(V1-X, Env), V1 == V, !.

extent_arg(E, int(X)) :-
   extent(E, X).

% work(+Kernel, +Ranges, -Global, -Local): the work items of Kernel, those of the ranged axes
% from their counts, and the items of a group, 0 for any.
work(Kernel, _, Global, Local), get_dict(kind, Kernel, items), get_dict(stage, Kernel, pack(Threads, _, _, _, _, _)) =>
   kernel{par: Par} :< Kernel,
   append(Batch, [_, _], Par), maplist(arg(2), Batch, Es), size(Es, NB),
   Global is Threads*NB,
   Local = 1.
work(Kernel, Values, Global, Local), get_dict(kind, Kernel, items) =>
   kernel{par: Par, stage: Stage} :< Kernel,
   maplist(axis_count(Values), Par, Ns),
   size(Ns, Global),
   group_size(Stage, Local).

work(Kernel, _, Global, Local), get_dict(kind, Kernel, groups), get_dict(item, Kernel, true) =>
   kernel{rows: Rows} :< Kernel,
   maplist(arg(2), Rows, Es),
   size(Es, Global),
   Local = 0.
work(Kernel, _, Global, Local), get_dict(kind, Kernel, groups) =>
   kernel{rows: Rows, local: Local} :< Kernel,
   maplist(arg(2), Rows, Es),
   size(Es, N),
   Global is N*Local.

axis_count(Values, I:_, N), member(I1-(_, Count), Values), I1 == I => N = Count.
axis_count(_, _:E, N) => extent(E, N).

group_size(none, Local) => Local = 0.
group_size(stage(G, _, _), Local) => Local is G*G.
group_size(pack(_, _, _, _, _, _), Local) => Local = 1.

% buffer_args(+Buffers, +N, +Args0, -Args): Args0 with N's buffer and offset as kernel arguments.
buffer_args(Buffers, N, Args0, Args) :-
   buffer_arg(Buffers, N, Mem, Off),
   append(Args0, [mem(Mem), int(Off)], Args).

% buffer_arg(+Buffers, +N, -Mem, -Off): the buffer holding N and N's element offset in it.
buffer_arg(Buffers, N, Mem, Off) :-
   member(N1-buf(Mem, Off), Buffers),
   N1 == N,
   !.

read_back(Queue, Buffers, Out, Values) :-
   buffer_arg(Buffers, Out, Mem, Off),
   shape(Out, Shape), size(Shape, N), Bytes is 4*N, ByteOff is 4*Off,
   ctype(Out, T), host_type(T, HT),
   buffer_alloc(Host, HT, N, true),
   buffer_offset(Host, HT, N, 0, Pointer),
   cl_read(Queue, Mem, ByteOff, Pointer, Bytes),
   buffer_to_data(Host, HT, N, Term),
   Term =.. [_ | Values].

% Allocation
% ==========

% allocate(+Context, +Queue, +Device, +Plan, +Out, +Data, +Options, -Alloc): a device buffer for
% every name of the plan. An input, a name no box writes or one given in Data, and Out have a
% buffer of their own, uploaded from Data or zeroed. The intermediates, with alloc(arena), the
% default, share one arena: each lives from the first kernel mentioning it to the last, and
% minimalloc lays the lifetimes out, see arena/10; with alloc(separate) each has a buffer of
% its own, zeroed. A name's place is its buffer and an element offset into it, which the
% kernels take as a pointer and an int: never a sub-buffer, which the NVIDIA runtime cannot
% release in either order once two overlapping ones have been kernel arguments. Alloc is a
% dict:
%   how      arena or separate,
%   buffers  Name-buf(Mem, Offset) pairs, every name of the plan, Offset in elements,
%   arena    the arena's buffer, or none,
%   bytes    the bytes the intermediates take: the arena, or their buffers,
%   apart    the bytes they take as buffers of their own,
%   peak     the most bytes live at one kernel, the floor of any arena,
%   setup    the seconds the intermediates took to allocate.
allocate(Context, Queue, Device, Plan, Out, Data, Options, Alloc) :-
   option(alloc(How), Options, arena),
   flat_plan(Plan, Kernels),
   foldl([K, Ns0, Ns]>>(get_dict(names, K, N1), append(Ns0, N1, Ns)), Kernels, [], Names0),
   list_to_set(Names0, Names),
   partition(intermediate(Out, Data), Names, Inter, Own),
   maplist(own_buffer(Context, Queue, Data), Own, OwnBuffers),
   cl_device_info(Device, mem_base_addr_align, Bits), Align is Bits // 8,
   maplist(aligned_bytes(Align), Inter, Sizes),
   sum_list(Sizes, Apart),
   lifetimes(Plan, Spans),
   length(Inter, N), ids(N, Ids),
   maplist(buffer_of(Spans), Ids, Inter, Sizes, Bufs),
   peak(Bufs, Peak),
   get_time(T0),
   arena(How, Context, Queue, Inter, Bufs, Align, Peak, InterBuffers, Arena, Bytes),
   get_time(T1), Setup is T1 - T0,
   append(OwnBuffers, InterBuffers, Buffers),
   Alloc = alloc{how: How, buffers: Buffers, arena: Arena, bytes: Bytes, apart: Apart, peak: Peak, setup: Setup}.

% own_buffer(+Context, +Queue, +Data, +Name, -Pair): Name's own buffer, at offset 0.
own_buffer(Context, Queue, Data, Name, Name-buf(Mem, 0)) :-
   device_buffer(Context, Queue, Data, Name, Mem).

% intermediate(+Out, +Data, +N): N is written by a box, is not Out, and has no data.
intermediate(Out, Data, N) :-
   N \== Out,
   boxes_of(N, [_ | _]),
   \+ ( member(N1-_, Data), N1 == N ).

ids(0, Ids) => Ids = [].
ids(N, Ids) => numlist(1, N, Ids).

% aligned_bytes(+Align, +Name, -Bytes): the bytes of Name's floats, rounded up to Align.
aligned_bytes(Align, Name, Bytes) :-
   shape(Name, Shape), size(Shape, N),
   Bytes is ((4*max(N, 1) + Align - 1) // Align) * Align.

% buffer_of(+Spans, +Id, +Name, +Size, -Buffer): the buffer term of minimalloc for Name: its
% lifetime is the kernels First to Last, the interval [First, Last+1).
buffer_of(Spans, Id, Name, Size, buffer(Id, First, End, Size, _)) :-
   member(N1-(First-Last), Spans), N1 == Name, !,
   End is Last + 1.

% peak(+Bufs, -Peak): the most bytes live at once: at the start of some buffer.
peak([], Peak) =>
   Peak = 0.
peak(Bufs, Peak) =>
   aggregate_all(max(Live),
                 ( member(buffer(_, T, _, _, _), Bufs),
                   aggregate_all(sum(S), ( member(buffer(_, S0, E, S, _), Bufs), S0 =< T, T < E ), Live) ),
                 Peak).

% lifetimes(+Plan, -Spans): Name-(First-Last) for every name of the plan: the positions, in
% source order, of the first and last kernel mentioning it. A name mentioned inside a host
% loop lives across the whole loop: a step may read what the previous step wrote.
lifetimes(Plan, Spans) :-
   spans(Plan, 0, _, [], Pairs),
   keysort(Pairs, Sorted),
   group_pairs_by_key(Sorted, Groups),
   maplist(span, Groups, Spans).

span(N-Is, N-(First-Last)) :-
   min_list(Is, First),
   max_list(Is, Last).

spans([], I, I1, Ps0, Ps) =>
   I1 = I, Ps = Ps0.
spans([loop(_, _, Inner) | Rest], I0, I, Ps0, Ps) =>
   spans(Inner, I0, I1, [], Inside),
   Last is I1 - 1,
   foldl(across(I0, Last), Inside, Ps0, Ps1),
   spans(Rest, I1, I, Ps1, Ps).
spans([K | Rest], I0, I, Ps0, Ps) =>
   get_dict(names, K, Names),
   foldl(at(I0), Names, Ps0, Ps1),
   I1 is I0 + 1,
   spans(Rest, I1, I, Ps1, Ps).

at(I, N, Ps, [N-I | Ps]).
across(First, Last, N-I, Ps, [N-First, N-Last, N-I | Ps]).

% arena(+How, +Context, +Queue, +Inter, +Bufs, +Align, +Peak, -Buffers, -Arena, -Bytes): the
% buffers of the intermediates. With arena, one buffer of Bytes, zeroed once, and each a
% sub-buffer of it at the offset minimalloc gives its lifetime, see packing/4: a name is
% written before it is read, so that the first occupant of a byte reads the zero the
% reference reads, and a later one what the previous left. With separate, a zeroed buffer each.
arena(arena, _, _, [], _, _, _, Buffers, Arena, Bytes) =>
   Buffers = [], Arena = none, Bytes = 0.
arena(arena, Context, Queue, Inter, Bufs, Align, Peak, Buffers, Arena, Bytes) =>
   packing(Bufs, Align, Peak, Bytes),
   cl_buffer(Context, Bytes, Arena),
   cl_fill(Queue, Arena, Bytes, [], Event),
   cl_wait([Event]),
   maplist(slice(Arena), Inter, Bufs, Buffers).
arena(separate, Context, Queue, Inter, Bufs, _, _, Buffers, Arena, Bytes) =>
   maplist(own_buffer(Context, Queue, []), Inter, Buffers),
   Arena = none,
   aggregate_all(sum(S), member(buffer(_, _, _, S, _), Bufs), Bytes).

% slice(+Arena, +Name, +Buffer, -Pair): Name's place in the arena, its byte offset in elements.
slice(Arena, Name, buffer(_, _, _, _, Offset), Name-buf(Arena, Elements)) :-
   Elements is Offset // 4.

% packing(+Bufs, +Align, +Peak, -Bytes): the offsets of Bufs under the least capacity, in units
% of Align, at which minimalloc finds a layout, by bisection between Peak, the most bytes live
% at once, which no layout beats, and the height of the layout under no capacity at all;
% Bytes that height.
packing(Bufs, Align, Peak, Bytes) :-
   arrange(Bufs, inf, Top, Offsets0),
   Lo is Peak // Align - 1,
   Hi is (Top + Align - 1) // Align,
   bisect(Bufs, Align, Lo, Hi, Offsets0, Offsets),
   maplist(offset_of, Bufs, Offsets),
   aggregate_all(max(H), ( member(buffer(_, _, _, S, O), Bufs), H is O + S ), Bytes).

offset_of(buffer(_, _, _, _, Offset), Offset).

% bisect(+Bufs, +Align, +Lo, +Hi, +Best0, -Best): Hi units is a capacity with the layout Best0,
% Lo one with none found; Best is the layout of the least capacity found between.
bisect(_, _, Lo, Hi, Best0, Best), Hi - Lo =< 1 =>
   Best = Best0.
bisect(Bufs, Align, Lo, Hi, Best0, Best) =>
   Mid is (Lo + Hi) // 2,
   Capacity is Mid*Align,
   (  arrange(Bufs, Capacity, _, Offsets)
   -> bisect(Bufs, Align, Lo, Mid, Offsets, Best)
   ;  bisect(Bufs, Align, Mid, Hi, Best0, Best)
   ).

% arrange(+Bufs, +Capacity, -Height, -Offsets): the offsets of a layout of Bufs under Capacity
% by the first of minimalloc's heuristics that finds one within an inference limit, and its
% height. Fails when none does. The search is on a copy, Bufs stay unbound.
arrange(Bufs, Capacity, Height, Offsets) :-
   member(Heuristic, [wat, taw, twa]),
   copy_term(Bufs, Trial),
   call_with_inference_limit(minimalloc(Trial, [capacity(Capacity), heuristics([Heuristic])]), 1_000_000, Result),
   Result \== inference_limit_exceeded,
   !,
   maplist(offset_of, Trial, Offsets),
   aggregate_all(max(H), ( member(buffer(_, _, _, S, O), Trial), H is O + S ), Height).

% Reference
% =========

% eval(+Out, +Data, -Values): the boxes of Out run in Prolog, exactly, on Data.
eval(Out, Data, Values) :-
   program(Out, Boxes),
   label_program(Out, Boxes),
   names(Boxes, Names0), list_to_set([Out | Names0], Names),
   findall(Vs, ( bind_extents(Boxes, Data),
                 maplist(host_buffer(Data), Names, Terms),
                 pairs_keys_values(Env, Names, Terms),
                 evaluate(Out, Boxes, Env, Vs) ),
           [Values]).

host_buffer(Data, Name, Term), member(Name1-List, Data), Name1 == Name =>
   ctype(Name, T), maplist(coerce(T), List, Elements),
   Term =.. [data | Elements].
host_buffer(_, Name, Term) =>
   shape(Name, Shape), size(Shape, N),
   length(Zeros, N), maplist(=(0), Zeros),
   Term =.. [data | Zeros].

