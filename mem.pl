:- module(mem, [allocation_plan/5]).

:- use_module(library(dcg/high_order)).
:- use_module(library(graphml_ugraph)).
:- use_module(library(clpfd)).
:- use_module(library(rbtrees)).
:- use_module(minimalloc).

:- use_module(buffer).

:- op(20, yf, []).
%
% dag(DAG) :-
%    DAG = [
%       n(n1, [b1[50]], [
%          n(n2, [b2[100]], [n(n7, [b7[100]])]),
%          n(n3, [b3[100]], [
%             n(n4, [b4[100]]),
%             n(n5, [b5[100]], [n(n6, [b6[100]])])
%          ])
%       ])
%    ].

% buffer_size(_[Size], Size).

interval(Start, Size, End) :-
   End #= Start + Size.

disjoint(S1, E1, S2, E2, Expr) :-
   Expr = (E1 #=< S2 #\/ E2 #=< S1).

intersect(S1, E1, S2, E2, Expr) :-
   disjoint(S1, E1, S2, E2, Disjoint),
   Expr = (#\ Disjoint).

conflicts([]).
conflicts([Buffer | Buffers]) :-
   maplist(conflict(Buffer), Buffers),
   conflicts(Buffers).
conflict(B1-[_, _, Start1, End1, PStart1, PEnd1],
         B2-[_, _, Start2, End2, PStart2, PEnd2]) :-
   (  B1 \== B2
   -> intersect(Start1, End1, Start2, End2, Intersect),
      disjoint(PStart1, PEnd1, PStart2, PEnd2, Disjoint),
      Intersect #==> Disjoint
   ;  true
   ).

window(N, Pivot, Rel, Vs) :-
   length(Vs, N),
   Vs ins 0..1,
   Pivot in 1..N,
   numlist(1, N, Us),
   maplist({Pivot, Rel}/[U, V]>>(
      Expr =.. [Rel, Pivot, U],
      V #<==> Expr), Us, Vs).

interval_window(N, Start, End, Vs) :-
   End1 #= End - 1,
   Start #< End,
   window(N, Start, #=<, Us),
   window(N, End1, #>=, Ws),
   maplist([U, W, V]>>(V #<==> (U #/\ W)), Us, Ws, Vs).

max(List, Rel, Res) :-
   fold_(max, List, Rel, Res).
min(Rel, List, Res) :-
   fold_(min, List, Rel, Res).

fold_(Op, [H | T], Rel, Result) :-
   foldl({Op}/[B, A, Next]>>(Next =.. [Op, A, B]), T, H, SubExpr),
   Expr =.. [Rel, SubExpr, Result],
   call(Expr).

rb_lookup(Key, Value), [NewT] -->
   [T],
   {  (  rb_lookup(Key, Value, T)
      -> T = NewT
      ;  rb_insert_new(T, Key, Value, NewT)
      )
   }.
rb_insert_(Key, Value), [NewT] -->
   [T],
   {rb_insert(T, Key, Value, NewT)}.
rb_update_(Key, OldValue, NewValue), [NewT] -->
   [T],
   {rb_update(T, Key, OldValue, NewValue, NewT)}.

dag_order(Arrays) -->
   sequence(dag_order_, Arrays).
dag_order_(Array) -->
   add_node(Array),
   sequence(dag_order_(Array), Array.inputs()).

dag_order_(Output, Input) -->
   dag_order_nodes(Output, Input),
   dag_order_buffers(Output, Input),
   dag_order_(Input).

add_node(Array) -->
   rb_lookup(Array, N),
   { Size #= Array.buffersize * Array.itemsize() },
   (  {var(Array.buffer)}
   -> add_node_to_buffer(N, Size, Array.buffer),
      {  maplist(get_dict(buffer), Array.inputs(), InputBuffers),
         include(var, InputBuffers, TrueInputBuffers)
      },
      sequence(add_node_to_buffer(N), TrueInputBuffers)
   ;  []
   ),
   (  {Array.is_input() = true}
   -> rb_update_(inputs, Inputs, [Array | Inputs])
   ;  []
   ).
add_node_to_buffer(N, Buffer) -->
   add_node_to_buffer(N, _, Buffer).
add_node_to_buffer(N, Size, Buffer) -->
   rb_lookup(Buffer, [Size, Ns | R]),
   {  (  var(Ns)
      -> Ns = []
      ;  true
      )
   },
   rb_insert_(Buffer, [Size, [N | Ns] | R]).

dag_order_nodes(OutputArray, InputArray) -->
   rb_lookup(OutputArray, Output),
   rb_lookup(InputArray, Input),
   {Output #> Input}.
dag_order_buffers(OutputArray, InputArray) -->
   (  {var(InputArray.buffer), OutputArray.buffer \== InputArray.buffer}
   -> rb_lookup(InputArray.buffer,  [_, _, _          , InputEnd | _]),
      rb_lookup(OutputArray.buffer, [_, _, OutputStart, _        | _]),
      { InputEnd #> OutputStart }
   ;  []
   ).

length_(Len, L) :-
   length(L, Len).

buffer_dict(buffer{size: Size, start: Start, end: End, pstart: P, data: _}-[Size, _, Start, End, P, _]).

allocation_plan(Arrays, Inputs, ExecutionPlan, BuffersDict, MaxAllocationSize) :-
   rb_new(T),
   rb_insert_new(T, inputs, [], T2),
   phrase(dag_order(Arrays), [T2], [T3]),
   rb_delete(T3, inputs, AllInputs, T1),
   sort(AllInputs, Inputs),
   rb_visit(T1, Pairs),

   partition([Term-_]>>is_dict(Term, array), Pairs, NodesPairs, BuffersPairs),

   pairs_values(NodesPairs, Nodes),
   length(Nodes, N),
   Nodes ins 1..N,
   maplist([Start, task(Start, 1, _, 1, _)]>>true, Nodes, Tasks),
   cumulative(Tasks),
   label(Nodes),
   pairs_keys_values(BuffersPairs, BuffersDict, Buffers),
   maplist(length_(6), Buffers),
   transpose(Buffers, [_BufferSizes, BufferNodes, Starts, Ends, _PStarts, PEnds]),
   maplist(min_list, BufferNodes, Starts),
   maplist(max_list, BufferNodes, Ends),
   maplist([[Size, _, Start, End, Offset, Height],
            buffer(_, Start, End, Size, Offset)]>>(Height #= Offset + Size),
           Buffers, Buffers2),
   minimalloc(Buffers2, [heuristics([wat]), capacity(inf)]),
   max_list(PEnds, MaxAllocationSize),
   same_length(NodesPairs, ExecutionPlan),
   maplist({ExecutionPlan}/[Node-Index]>>nth1(Index, ExecutionPlan, Node), NodesPairs),
   maplist(buffer_dict, BuffersPairs).
