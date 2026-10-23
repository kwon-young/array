:- module(array, [
   op(700, xfx, @=),
   op(400, yfx, @),
   '@='/2
]).

/** <module> N-dimensional arrays

An array is a lazy node of a computation graph, read through a stack of
views.
Two kinds of constraints describe it:

  * Its shape, and the strides, masks and offsets of its views, are clpfd
    relations: they may be unknown, constrained by the user, and queried
    backwards, as a search over the arrays an op can build.
    On integers, every op is det.
  * Its range, enclosing its values, and its precision, bounding its
    error, are clpBNR analyses: the user defines them on leaves only, as
    true enclosures of their data, and never narrows them afterwards.
    The library creates them forward, on fresh variables, when it pushes
    an op, and never narrows an existing one either: a narrowing would
    propagate back through ops whose inputs it says nothing true about, as
    a sum or a selection, and formats are chosen from ranges.
*/

:- use_module(library(lists), except([flatten/2])).
:- use_module(library(clpfd), except([transpose/2, sum/3])).
:- use_module(library(pairs)).
:- use_module(library(dcg/high_order)).
:- use_module(library(clpBNR)).
:- use_module(library(rbtrees)).
:- use_module(view).
:- use_module(dtype).
:- use_module(minimalloc).

:- multifile compile/4.
:- multifile allocate/2.
% :- multifile dtype/3.
% :- multifile broadcast_dtype/3.
:- multifile to/4.
:- multifile dtype_size/3.
:- multifile default_format/3.
:- multifile float_formats/2.
:- multifile expression_op/2.
:- multifile compute_format/3.

:- use_module(runtime_prolog).
:- use_module(runtime_c).
:- use_module(runtime_opencl).
% after the runtimes: the lup tests need to run before clpBNR first sets its
% arithmetic flags
:- use_module(precision).
:- use_module(fusion).

sync_clpfd_clpBNR(Var) :-
   fd_inf(Var, FDMin),
   (  FDMin == inf
   -> Min = -inf
   ;  Min = FDMin
   ),
   fd_sup(Var, FDMax),
   (  FDMax == sup
   -> Max = inf
   ;  Max = FDMax
   ),
   Var::integer(Min, Max).

% Creation
% ========
M.default() := Dict :-
   Dict = M.default([]).
M.default(Options) := Dict :-
   dict_options(M, MOptions),
   merge_options(Options, MOptions, Merged),
   option(dtype(DType), Merged, float),
   Range::real(-inf, inf),
   option(range(Range), Merged, _),
   option(device(Device), Merged, prolog),
   option(data(Data), Options, _),
   option(format(Format), Options, _),
   % leaf data is exact unless the user declares its error
   option(precision(Precision), Options, 0),
   (  option(shape(Shape), Merged)
   -> View = view{}.from_shape(Shape),
      DataSize = View.size(),
      Views = [View]
   ;  Views = []
   ),
   Dict = array{id: _, views: Views, device:Device, data: Data, format: Format,
                datasize: DataSize, op: true, range: Range, dtype: DType,
                precision: Precision}.

M.empty(Shape) := Dict :-
   Dict = M.empty(Shape, []).
M.empty(Shape, Options) := Dict :-
   Dict = M.default([shape(Shape) | Options]).

M.fromlist(List) := Dict :-
   Dict = M.fromlist(List, []).
M.fromlist(List, Options) := Dict :-
   list_shape(List, Shape),
   flatten(List, Flat),
   select_option(device(Device), Options, Options1, prolog),
   foldl([X, In, Out]>>(
      get_dtype(X, DType_),
      broadcast_dtype(DType_, In, Out)
   ), Flat, boolean, ListDType),
   select_option(dtype(DType), Options1, RestOptions, ListDType),
   min_list(Flat, Min),
   max_list(Flat, Max),
   Range::real(Min, Max),
   compound_name_arguments(Data, data, Flat),
   M1 = M.empty(Shape, [device(prolog), range(Range), dtype(ListDType), data(Data) | RestOptions]),
   Dict = M1.to(Device).as(DType).
list_shape(L, Shape) :-
   list_shape_(Shape, L).
list_shape_(Shape, L), is_list(L) =>
   length(L, Dim),
   Shape = [Dim | Dims],
   maplist(list_shape_(Dims), L).
list_shape_(Shape, _) => Shape = [].

M.full(Shape, Value) := Dict :-
   Dict = M.full(Shape, Value, []).
M.full(Shape, Value, Options) := Dict :-
   Dict = M.push(constant(Value, Options)).expand(Shape).

M.zeros(Shape) := Dict :-
   Dict = M.zeros(Shape, []).
M.zeros(Shape, Options) := Dict :-
   Dict = M.full(Shape, 0, Options).

M.ones(Shape) := Dict :-
   Dict = M.ones(Shape, []).
M.ones(Shape, Options) := Dict :-
   Dict = M.full(Shape, 1, Options).

M.arange(Stop) := Dict :-
   Dict = M.arange(Stop, []).
M.arange(Stop, Options) := Dict :-
   Dict = M.arange(0, Stop, Options).
M.arange(Start, Stop, Options) := Dict :-
   Dict = M.arange(Start, Stop, 1, Options).
M.arange(Start, Stop, Step, Options) := Dict :-
   N is ceil((Stop - Start) / Step),
   M1 = M.full([N], Step, Options),
   M2 @= M1.cumalu(0, +) + (Start - Step),
   End is Start + (N - 1) * Step,
   Min is min(Start, End),
   Max is max(Start, End),
   Range::real(Min, Max),
   Dict = M2.put(range, Range).

M.eye(N) := Dict :-
   Dict = M.eye(N, []).
M.eye(N, Options) := Dict :-
   Dict = M.eye(N, N, Options).
M.eye(N, M_, Options) := Dict :-
   A = M.arange(N, Options),
   Dict @= (A.unsqueeze(A.ndim()) =:= M.arange(M_, Options)).

M.rand(Shape) := Dict :-
   Dict = M.rand(Shape, []).
M.rand(Shape, Options) := Dict :-
   Dict = M.push(rand(Shape, Options)).

M.randn(Shape) := Dict :-
   Dict = M.randn(Shape, []).
M.randn(Shape, Options) := Dict :-
   U1 = M.rand(Shape, Options),
   U2 = M.rand(Shape, Options),
   Pi is pi,
   Dict @= cos(2*Pi*U1) * sqrt(-2*log(1-U2)).

% Movement
% ========
% numpy's basic indexing, as a relation: Index holds an item per dim, from
% the first, missing items reading their whole dim:
%   * an integer I, -Dim =< I < Dim, from the end when negative, drops its
%     dim; I may be a clpfd variable, and an index out of its dim fails;
%   * Start:End or Start:End:Step slices its dim, clamping Start and End
%     as numpy; inf and sup are bounds before the first and past the last
%     index; Step is not 0, and reads backwards when negative;
%   * : reads the whole dim, as inf:sup:1;
%   * new adds a dim of size 1;
%   * an array of integers, or a list of them, selects elements of its dim
%     by value; the index arrays broadcast together, and their dims replace
%     the dims they index, in place when the integers and arrays of Index
%     are adjacent, else first, as numpy.
%     The range of an index array must prove its indices are in their dim,
%     -Dim =< I < Dim: an index that may be out of it fails.
M.index(Index) := Dict :-
   index_dims(Index, M.shape(), Shrinks, Flags, Steps, Dims),
   exclude(==(dropped), Dims, Kept),
   maplist(result_dim, Kept, Shape),
   M1 = M.shrink(Shrinks).flip(Flags).stride(Steps).reshape(Shape),
   indexed_dims(Kept, 0, Indexed),
   maplist(advanced, Dims, Advanced),
   gather(Indexed, Advanced, M1, Dict).

% B is A with the elements A.index(Index) reads replaced by Values, which
% broadcast to their shape: Index is as in index/1. When index arrays write
% an element several times, the last write in the order of their broadcast
% shape wins. Values may be an array,
% a number or a list, cast to the dtype of A when nothing is lost: a
% boolean to an integer or a float, an integer to a float when its range
% lies within +-2**53; an index_put that would lose precision fails.
A.index_put(Index, Values) := B :-
   index_dims(Index, A.shape(), Shrinks, Flags, Steps, Dims),
   exclude(==(dropped), Dims, Kept),
   maplist(result_dim, Kept, Shape),
   indexed_dims(Kept, 0, Indexed),
   maplist(advanced, Dims, Advanced),
   value_array(Values, A, V0),
   upcast(V0, A.dtype, V),
   written(Indexed, Advanced, Shape, A.device, V, Written, Values1),
   Strided = A.shrink(Shrinks).flip(Flags).stride(Steps),
   Placement = placement(Strided.shape(), Shrinks, Flags, Steps, A.shape()),
   place(Placement, Values1, Placed),
   place(Placement, Written, Mask),
   B @= where(Mask, Placed, A).

% An array of values on the device of A.
value_array(Values, _, V), is_dict(Values, array) =>
   V = Values.
value_array(Values, A, V), is_list(Values) =>
   V = array{}.fromlist(Values, [device(A.device)]).
value_array(Values, A, V), number(Values) =>
   V = array{}.full([], Values, [device(A.device)]).

% V1 is V in DType, cast when nothing is lost.
upcast(V, DType, V1), get_dict(dtype, V, DType) =>
   V1 = V.
upcast(V, float, V1), get_dict(dtype, V, integer) =>
   range_min_max(V.range, Min, Max),
   Bound is 2**53,
   Min >= -Bound,
   Max =< Bound,
   V1 = V.as(float).
upcast(V, DType, V1), get_dict(dtype, V, boolean) =>
   V1 = V.as(DType).
upcast(_, _, _) =>
   fail.

% place(+Placement, +X, -Y)
% Y is X, of the shape A.index(Index) reads, placed where it reads it in A:
% the inverse of its shrink, flip, stride and reshape, reading 0 elsewhere.
place(placement(StridedShape, Shrinks, Flags, Steps, Shape), X, Y) :-
   X1 = X.reshape(StridedShape),
   maplist([Lo-Hi, Size]>>(Size #= Hi - Lo), Shrinks, Sizes),
   length(Shape, NDim),
   axes(NDim, Axes),
   foldl(dilate, Axes, Steps, Sizes, X1, X2),
   X3 = X2.flip(Flags),
   maplist([Lo-Hi, Dim, Lo-After]>>(After #= Dim - Hi), Shrinks, Shape, Pads),
   Y = X3.pad(Pads).

% Axes are the axes of NDim dims.
axes(0, Axes) =>
   Axes = [].
axes(NDim, Axes) =>
   Last is NDim - 1,
   numlist(0, Last, Axes).

% dilate(+Axis, +K, +Size, +X0, -X): index j of the dim Axis of X0 moves to
% j*K in a dim of size Size, its gaps reading 0: the inverse of stride.
dilate(Axis, K, Size, X0, X) :-
   Shape0 = X0.shape(),
   nth0(Axis, Shape0, N),
   Axis1 is Axis + 1,
   nth0(Axis1, Unit, 1, Shape0),
   length(Shape0, NDim),
   length(Pads, NDim),
   maplist(=(0-0), Pads),
   K1 #= K - 1,
   nth0(Axis1, Pads1, 0-K1, Pads),
   X1 = X0.reshape(Unit).pad(Pads1),
   NK #= N*K,
   replace_nth0(NK, Axis, Shape0, Merged),
   X2 = X1.reshape(Merged),
   maplist([D, 0-D]>>true, Merged, Shrink0),
   replace_nth0(0-Size, Axis, Shrink0, Shrink),
   X = X2.shrink(Shrink).

index_dims([], [], Shrinks, Flags, Steps, Shape) =>
   Shrinks = [],
   Flags = [],
   Steps = [],
   Shape = [].
index_dims([], Dims, Shrinks, Flags, Steps, Shape) =>
   index_dims([:], Dims, Shrinks, Flags, Steps, Shape).
index_dims([I | Items], [Dim | Dims], Shrinks, Flags, Steps, Shape),
      ( var(I) ; integer(I) ) =>
   position(I, Dim, P),
   P1 #= P + 1,
   Shrinks = [P-P1 | Shrinks1],
   Flags = [0 | Flags1],
   Steps = [1 | Steps1],
   Shape = [dropped | Shape1],
   index_dims(Items, Dims, Shrinks1, Flags1, Steps1, Shape1).
% A dim indexed by an array stays whole until the gather.
index_dims([A | Items], [Dim | Dims], Shrinks, Flags, Steps, Shape),
      ( is_list(A) ; is_dict(A, array) ) =>
   Shrinks = [0-Dim | Shrinks1],
   Flags = [0 | Flags1],
   Steps = [1 | Steps1],
   Shape = [indexed(Dim, A) | Shape1],
   index_dims(Items, Dims, Shrinks1, Flags1, Steps1, Shape1).
index_dims([new | Items], Dims, Shrinks, Flags, Steps, Shape) =>
   Shape = [1 | Shape1],
   index_dims(Items, Dims, Shrinks, Flags, Steps, Shape1).
index_dims([Slice | Items], [Dim | Dims], Shrinks, Flags, Steps, Shape) =>
   slice(Slice, Dim, Shrink, Flag, Step, Dim1),
   Shrinks = [Shrink | Shrinks1],
   Flags = [Flag | Flags1],
   Steps = [Step | Steps1],
   Shape = [Dim1 | Shape1],
   index_dims(Items, Dims, Shrinks1, Flags1, Steps1, Shape1).
% More items than dims: no index.
index_dims([_ | _], [], _, _, _, _) =>
   fail.

result_dim(indexed(Dim, _), D) =>
   D = Dim.
result_dim(Dim, D) =>
   D = Dim.

% An integer or an array is an advanced item of an index: 1.
advanced(Dim, A), Dim == dropped => A = 1.
advanced(indexed(_, _), A) => A = 1.
advanced(_, A) => A = 0.

% Indexed holds Position-IndexArray for each dim indexed by an array.
indexed_dims([], _, Indexed) =>
   Indexed = [].
indexed_dims([indexed(_, A) | Dims], P, Indexed) =>
   Indexed = [P-A | Indexed1],
   P1 is P + 1,
   indexed_dims(Dims, P1, Indexed1).
indexed_dims([_ | Dims], P, Indexed) =>
   P1 is P + 1,
   indexed_dims(Dims, P1, Indexed).

% gather(+Indexed, +Advanced, +X, -Y)
% Y reads X through the index arrays of Indexed, as one-hot masks: the
% indexed dims of X merge into one dim of size N, the index arrays into one
% linear index L, and Y sums where(L =:= arange(N), X, 0) over that dim.
gather([], _, X, Y) =>
   Y = X.
gather(Indexed, Advanced, X, Y) =>
   indexed_block(Indexed, Advanced, X.shape(), X.device,
                 block(Permutation, Pre, _, Post, B, N, L)),
   append([Pre, [N], Post], MergedShape),
   X1 = X.permute(Permutation).reshape(MergedShape),
   one_hot(B, N, L, X.device, Hit),
   ones(Pre, OnesPre),
   ones(Post, OnesPost),
   ones(B, OnesB),
   append([OnesPre, B, [N], OnesPost], HitShape),
   append([Pre, OnesB, [N], Post], XShape),
   Selected @= where(Hit.reshape(HitShape), X1.reshape(XShape), 0),
   length(Pre, NPre),
   length(B, NB),
   Axis is NPre + NB,
   selection_sum([Axis], Selected, Sum),
   Y = Sum.as(X.dtype).

% written(+Indexed, +Advanced, +Shape, +Device, +V, -Mask, -Placed)
% Mask and Placed, of Shape, are the elements an index_put writes and their
% values V, for the index arrays of Indexed: the one-hot masks of a gather,
% read the other way. When several indices write one element, the last one
% in the order of their broadcast shape wins.
written([], _, Shape, Device, V, Mask, Placed) =>
   Placed = V.expand(Shape),
   Mask = array{}.ones(Shape, [device(Device)]).
written(Indexed, Advanced, Shape, Device, V0, Mask, Placed) =>
   indexed_block(Indexed, Advanced, Shape, Device,
                 block(Permutation, Pre, Dims, Post, B, N, L)),
   append([Pre, B, Post], Target),
   V = V0.expand(Target),
   one_hot(B, N, L, Device, Hit),
   % the rank of each index, from 1 in row-major order
   foldl([D, S0, S1]>>(S1 is S0*D), B, 1, Size),
   Size1 is Size + 1,
   append(B, [1], BOne),
   Rank = array{}.arange(1, Size1, [device(Device)]).reshape(BOne),
   Score @= where(Hit, Rank, 0),
   length(B, NB),
   axes(NB, BAxes),
   max_over(BAxes, Score, Last),
   Wins @= where(Hit, Rank =:= Last, 0),
   ones(Pre, OnesPre),
   ones(Post, OnesPost),
   append([OnesPre, B, [N], OnesPost], WinsShape),
   append([Pre, B, [1], Post], VShape),
   Selected @= where(Wins.reshape(WinsShape), V.reshape(VShape), 0),
   length(Pre, NPre),
   numlist_from(NPre, NB, SumAxes),
   selection_sum(SumAxes, Selected, Values0),
   Values = Values0.as(V.dtype),
   Written @= (Last > 0),
   append([OnesPre, [N], OnesPost], WrittenShape),
   append([Pre, [N], Post], MergedShape),
   append([Pre, Dims, Post], Shape1),
   inverse_permutation(Permutation, Inverse),
   Placed = Values.reshape(Shape1).permute(Inverse),
   Mask0 = Written.reshape(WrittenShape).expand(MergedShape),
   Mask = Mask0.reshape(Shape1).permute(Inverse).

max_over([], X, Y) =>
   Y = X.
max_over(Axes, X, Y) =>
   Y = X.max(Axes).

% selection_sum(+Axes, +Terms, -Sum)
% Sum is the sum of Terms over Axes, of which at most one term is not 0, as
% the selections of a one-hot mask: an element of Sum is an element of
% Terms, so Sum has the range of Terms, and rounds once. Its op is a sum.
selection_sum([], Terms, Sum) =>
   Sum = Terms.
selection_sum(Axes, Terms, Sum) =>
   foldl(replace_nth0(1), Axes, Terms.shape(), Shape),
   sort(Axes, Axes1),
   broadcast_dtype(Terms.dtype, integer, DType),
   M0 = Terms.empty(Shape, [range(Terms.range), dtype(DType)]),
   precision:selection_precision(M0.put([id: _, op: reduce(+, Axes1, Terms)]), Terms, M),
   Sum = M.squeeze(Axes1).

% Axes are the N axes from First.
numlist_from(_, 0, Axes) =>
   Axes = [].
numlist_from(First, N, Axes) =>
   Last is First + N - 1,
   numlist(First, Last, Axes).

% Hit, of shape B ++ [N], holds L =:= arange(N).
one_hot(B, N, L, Device, Hit) :-
   append(B, [1], BOne),
   Hit @= (L.reshape(BOne) =:= array{}.arange(N, [device(Device)])).

% indexed_block(+Indexed, +Advanced, +Shape, +Device, -Block)
% Block = block(Permutation, Pre, Dims, Post, B, N, L) for the dims of
% Shape the index arrays of Indexed index: Permutation moves them after the
% dims Pre, in place when the advanced items are adjacent, else first; Dims
% are their sizes, of product N, B the broadcast shape of the index arrays
% and L their linear index.
indexed_block(Indexed, Advanced, Shape, Device,
              block(Permutation, Pre, Dims, Post, B, N, L)) :-
   pairs_keys_values(Indexed, Positions, Arrays0),
   maplist(index_array(Device), Arrays0, Arrays1),
   broadcast(Arrays1, Arrays2),
   [B0 | _] = Arrays2,
   B = B0.shape(),
   maplist([P, Dim]>>nth0(P, Shape, Dim), Positions, Dims),
   maplist(in_dim, Arrays2, Dims, Arrays),
   length(Shape, NDim),
   front_permutation(Advanced, Positions, NDim, Permutation, Front),
   maplist([P, Dim]>>nth0(P, Shape, Dim), Permutation, Shape1),
   length(Dims, K),
   NPost is NDim - Front - K,
   length(Pre, Front),
   length(Block, K),
   length(Post, NPost),
   append([Pre, Block, Post], Shape1),
   foldl([D, N0, N1]>>(N1 is N0*D), Dims, 1, N),
   linear_index(Arrays, Dims, L).

% An index array is an array of integers, on the device of the array it
% indexes.
index_array(Device, List, A), is_list(List) =>
   A = array{}.fromlist(List, [device(Device), dtype(integer)]).
index_array(_, A0, A), get_dict(dtype, A0, integer) =>
   A = A0.
index_array(_, A0, _) =>
   type_error(integer_index_array, A0).

% The range of an index array must prove its indices are in their dim: an
% index that may be out of it fails. A negative index reads from the end.
in_dim(I, Dim, I1) :-
   must_be(integer, Dim),
   range_min_max(I.range, Min, Max),
   Min >= -Dim,
   Max < Dim,
   from_end_index(Min, Dim, I, I1).

from_end_index(Min, _, I, I1), Min >= 0 =>
   I1 = I.
from_end_index(_, Dim, I, I1) =>
   I1 @= I + Dim*(I < 0).

% The indexed dims start at Front after Permutation: in place when the
% advanced items are adjacent, else first.
front_permutation(Advanced, Positions, NDim, Permutation, Front),
      adjacent(Advanced) =>
   axes(NDim, Permutation),
   Positions = [Front | _].
front_permutation(_, Positions, NDim, Permutation, Front) =>
   axes(NDim, Axes),
   subtract(Axes, Positions, Others),
   append(Positions, Others, Permutation),
   Front = 0.

% Inverse undoes the permute of Permutation.
inverse_permutation(Permutation, Inverse) :-
   length(Permutation, NDim),
   axes(NDim, Axes),
   pairs_keys_values(Pairs, Permutation, Axes),
   keysort(Pairs, Sorted),
   pairs_values(Sorted, Inverse).

% The 1s of Advanced are one run.
adjacent(Advanced) :-
   append(Before, [1 | Rest], Advanced),
   maplist(==(0), Before),
   append(Ones, After, Rest),
   maplist(==(1), Ones),
   maplist(==(0), After),
   !.

% L is the row-major position of the indices of Arrays in the dims Dims.
linear_index(Arrays, Dims, L) :-
   foldl([A, D, L0, L1]>>(L1 @= L0*D + A), Arrays, Dims, 0, L).

ones(List, Ones) :-
   same_length(List, Ones),
   maplist(=(1), Ones).

% P is the position of the index I of a dim.
position(I, Dim, P) :-
   -Dim #=< I,
   I #< Dim,
   Negative #<==> (I #< 0),
   P #= I + Negative*Dim.

slice(:, Dim, Shrink, Flag, Step, Dim1) =>
   slice(inf:sup:1, Dim, Shrink, Flag, Step, Dim1).
slice(Start:(End:K), Dim, Shrink, Flag, Step, Dim1) =>
   slice(Start, End, K, Dim, Shrink, Flag, Step, Dim1).
slice(Start:End, Dim, Shrink, Flag, Step, Dim1) =>
   slice(Start, End, 1, Dim, Shrink, Flag, Step, Dim1).
slice(Item, _, _, _, _, _) =>
   type_error(index_item, Item).

% A slice reads the indices from Start by steps of K, before End: a shrink
% to them, flipped when K is negative, and strided by abs(K).
slice(Start0, End0, K, Dim, Lo-Hi, Flag, Step, Dim1) :-
   bound(Start0, Dim, Start1),
   bound(End0, Dim, End1),
   K #\= 0,
   Flag #<==> (K #< 0),
   Step #= abs(K),
   from_end(Start1, Dim, Start2),
   from_end(End1, Dim, End2),
   clamp(Flag, Dim, Start2, Start),
   clamp(Flag, Dim, End2, End),
   Hi #= Flag*(Start + 1) + (1 - Flag)*max(Start, End),
   Lo #= Flag*min(End + 1, Hi) + (1 - Flag)*Start,
   Dim1 #= (Hi - Lo + Step - 1) // Step.

% inf is before the first index and sup past the last one, whatever the
% direction.
bound(B, _, V), var(B) =>
   V = B.
bound(B, _, V), integer(B) =>
   V = B.
bound(inf, Dim, V) =>
   V #= -Dim - 1.
bound(sup, Dim, V) =>
   V = Dim.
bound(B, _, _) =>
   type_error(slice_bound, B).

from_end(B, Dim, V) :-
   Negative #<==> (B #< 0),
   V #= B + Negative*Dim.

% Forwards, a bound lies in 0..Dim; backwards, in -1..Dim-1.
clamp(Flag, Dim, B, V) :-
   V #= Flag*max(-1, min(Dim - 1, B)) + (1 - Flag)*max(0, min(Dim, B)).

M.reshape(Shape) := Dict :-
   reshape_array(M, M.view(), Shape, Dict).

% Only integers decide a merge into the top view: a merge would constrain
% unknown dims, strides or masks, while a pushed view holds for any.
reshape_array(M, View, Shape, Dict), ground(View-Shape),
      merged_view(View, Shape, Merged) =>
   Dict = M.replace_view(Merged).
reshape_array(M, _, Shape, Dict) =>
   view:shape_size(Shape, M.size()),
   Dict = M.push_view(view{}.from_shape(Shape)).

merged_view(View, Shape, Merged) :-
   Merged = View.reshape(Shape).

M.t() := Dict :-
   Dict = M.transpose().
M.transpose() := Dict :-
   Dict = M.replace_view(M.view().transpose()).

M.swapaxes(Axis1, Axis2) := Dict :-
   Dict = M.replace_view(M.view().swapaxes(Axis1, Axis2)).

M.permute(Axes) := Dict :-
   Dict = M.replace_view(M.view().permute(Axes)).

M.expand(Shape) := Dict :-
   Dict = M.replace_view(M.view().expand(Shape)).

M.squeeze() := Dict :-
   findall(Axis, nth0(Axis, M.shape(), 1), Axes),
   Dict = M.squeeze(Axes).
% A reshape: a dim of padding stays below, in a view of its own.
M.squeeze(Axes) := Dict :-
   sort(0, @>, Axes, Axes_),
   foldl([Axis, In, Out]>>nth0(Axis, In, 1, Out), Axes_, M.shape(), Shape),
   Dict = M.reshape(Shape).

M.unsqueeze(Axis) := Dict :-
   nth0(Axis, Shape, 1, M.shape()),
   Dict = M.reshape(Shape).

M.shrink(Shrink) := Dict :-
   Dict = M.replace_view(M.view().shrink(Shrink)).

M.flip(Flags) := Dict :-
   Dict = M.replace_view(M.view().flip(Flags)).

M.stride(Steps) := Dict :-
   Dict = M.replace_view(M.view().stride(Steps)).

M.flatten_() := Dict :-
   Dict = M.reshape([M.size()]).

M.pad(Padding) := Dict :-
   Dict = M.pad(Padding, []).

M.pad(Padding, Options) := Dict :-
   M1 = M.replace_view(M.view().pad(Padding)),
   (  option(constant(Value), Options), Value #\= 0
   -> Mask_ = M.ones(M.shape()),
      Mask @= 1 - Mask_.replace_view(Mask_.view().pad(Padding)),
      Dict @= M1 + Mask*Value
   ;  B::boolean,
      { Range is M.range * B + 0 * (1 - B) },
      Dict = M1.put([range(Range)])
   ).

M.repeat(Repeat) := Dict :-
   foldl([D, [1, D | Out], Out]>>true, M.shape(), UnsqueezedShape, []),
   foldl([R, D, F, [R, D | Out], Out]>>(F #= R*D),
         Repeat, M.shape(), FinalShape, ExpandedShape, []),
   Dict = M.reshape(UnsqueezedShape).expand(ExpandedShape).reshape(FinalShape).

M.pool(Kernel) := Dict :-
   Dict = M.pool(Kernel, []).
M.pool(Kernel, Options) := Dict :-
   length(Kernel, N),
   option(strides(Strides_), Options, []),
   lpad(N, 1, Strides_, Strides),
   option(dilations(Dilations_), Options, []),
   lpad(N, 1, Dilations_, Dilations),
   same_length(Kernel, LastDims),
   once(append(PrefixDims, LastDims, M.shape())),

   maplist(same_length(Kernel), [Output, StridesOutput, Fs, Unfolded, Target, Repeat]),
   clpfd:transpose([
      LastDims, Kernel, Dilations, Strides,
      Output, StridesOutput, Fs, Unfolded, Target, Repeat], Args),
   maplist(prepare_pool, Args),
      
   lpad(M.ndim(), 1, Repeat, PaddedRepeat),
   M1 = M.repeat(PaddedRepeat),

   M2 = M1.pool_shrink_reshape(PrefixDims, [Target], [Kernel, Unfolded]),

   M3 = M2.pool_shrink_reshape(PrefixDims, [Kernel, StridesOutput], [Kernel, Output, Strides]),

   lpad(N, 1, [], Ones),
   M4 = M3.pool_shrink_reshape(PrefixDims, [Kernel, Output, Ones], [Kernel, Output]),

   numlist(0, M4.ndim0(), Axes),
   same_length(PrefixDims, PrefixAxes),
   append(PrefixAxes, PoolAxes, Axes),
   once(foldl([A, B, [A, B | R], R]>>true, KernelAxes, DimAxes, PoolAxes, [])),
   append([PrefixAxes, DimAxes, KernelAxes], PermuteAxes),
   Dict = M4.permute(PermuteAxes).
prepare_pool([Dim, KernelDim, Dilation, Stride, OutputDim, StrideOutputDim,
              F, Unfolded, Target, Repeat]) :-
   E #= Dim - Dilation*(KernelDim - 1),
   OutputDim #= (E - 1) // Stride + 1,
   StrideOutputDim #= OutputDim*Stride,
   (StrideOutputDim #> E) #<==> B, F #= 1 + B,
   Unfolded #= Dim*F+Dilation,
   Target #= KernelDim*Unfolded,
   ceildiv(Target, Dim, Repeat).
M.pool_shrink_reshape(PrefixDims, Shrink, Reshape) := Dict :-
   concat_prefix(Shrink, PrefixDims, PrefixedShrink),
   lpad(M.ndim(), 0, [], Zeros),
   pairs_keys_values(ShrinkPairs, Zeros, PrefixedShrink),
   M1 = M.shrink(ShrinkPairs),

   concat_prefix(Reshape, PrefixDims, PrefixedReshape),
   Dict = M1.reshape(PrefixedReshape).
concat_prefix(In, Prefix, Out) :-
   clpfd:transpose(In, T),
   flatten(T, Flat),
   append(Prefix, Flat, Out).
ceildiv(A, B, C) :-
   C #= (A+B-1)//B.

M.diag() := Dict :-
   M.shape() = [N],
   N2 is N*N,
   Dict = M.unsqueeze(1).pad([0-0, 0-N]).flatten_().shrink([0-N2]).reshape([N, N]).

% Conversion
% ==========
M.tolist() := List :-
   List = M.tolist([]).
% Options are passed to realize/1.
M.tolist(Options) := List :-
   shape_list(M.shape(), List),
   flatten(List, Flat),
   M1 = M.contiguous().realize(Options),
   M2 = M1.to(prolog).realize(),
   data_slice(M2.data, M2.data_offset(), Flat).

% Flat is the slice of the arguments of Data from Offset.
data_slice(_, _, Flat), Flat == [] =>
   true.
data_slice(Data, Offset, Flat) =>
   compound_name_arguments(Data, data, Args),
   length(Prefix, Offset),
   append(Prefix, Rest, Args),
   append(Flat, _, Rest).

shape_list([], _).
shape_list([Dim | Shape], L) :-
   length(L, Dim),
   maplist(shape_list(Shape), L).

% Ops
% ===
push(view(Views), M, Dict) :-
   M1 = M.put(views, Views),
   (  M.op = view(_)
   -> Dict = M1
   ;  Dict = M1.push_op(view(M))
   ).
push(constant(Value, Options), M, Dict) :-
   get_dtype(Value, ValueDType),
   select_option(dtype(DType), Options, RestOptions, ValueDType),
   M1 = M.empty([], [range(Value), dtype(ValueDType) | RestOptions]),
   Dict = M1.push_op(constant(Value)).as(DType).
push(rand(Shape, Options), M, Dict) :-
   Range::real(0, 1),
   Dict = M.empty(Shape, [range(Range), dtype(float) | Options]).push_op(rand).
push(contiguous, M, Dict) :-
   Dict = M.empty(M.shape()).push_op(contiguous(M)).
push(reduce(Op, Axes), M, Dict) :-
   check_identity(Op, M.shape(), Axes),
   foldl(replace_nth0(1), Axes, M.shape(), Shape),
   sort(Axes, Axes_),
   (  Op == (<)
   -> % a maximum is one of the elements
      DType = M.dtype,
      { Range == M.range }
   ;  view:shape_size(M.shape(), Size1),
      view:shape_size(Shape, Size2),
      N #= Size1 // Size2,
      sync_clpfd_clpBNR(N),
      broadcast_dtype(M.dtype, integer, DType),
      (  Op == (+)
      -> { Range == M.range * N }
      )
   ),
   Dict = M.empty(Shape, [range(Range), dtype(DType)]).push_op(reduce(Op, Axes_, M)).
% A maximum has no identity: like numpy, it can't reduce an empty axis.
check_identity(<, Shape, Axes), member(Axis, Axes), nth0(Axis, Shape, 0) =>
   domain_error(non_empty_axes, Axes).
check_identity(_, _, _) =>
   true.

push(float(A), C) :-
   push(elementwise(float, [A]), C).
push(integer(A), C) :-
   push(elementwise(integer, [A]), C).
push(A+B, C) :-
   push(elementwise(+, [A, B]), C).
push(A*B, C) :-
   push(elementwise(*, [A, B]), C).
push(A<B, C) :-
   push(elementwise(<, [A, B]), C).
push(sin(A), C) :-
   push(elementwise(sin, [A.as(float)]), C).
push(log(A), C) :-
   push(elementwise(log, [A.as(float)]), C).
push(sqrt(A), C) :-
   push(elementwise(sqrt, [A.as(float)]), C).
push(elementwise(Op, Args), C) :-
   (  dicts_same_value_for_key(Args, device, _Device)
   -> true
   ;  type_error(device, Args)
   ),
   (  Op == (<)
   -> FinalDType = boolean
   ;  Op == float
   -> FinalDType = float
   ;  Op == integer
   -> FinalDType = integer
   ;  maplist(get_dict(dtype), Args, DTypes),
      foldl(broadcast_dtype, DTypes, integer, FinalDType)
   ),
   maplist(get_dict(range), Args, Ranges),
   (  (Op == float ; Op == integer)
   -> Args = [M],
      range_min_max(M.range, Min, Max),
      cast(FinalDType, Min, Min1),
      cast(FinalDType, Max, Max1),
      Range::real(Min1, Max1)
   ;  Expr =.. [Op | Ranges],
      {Range is Expr}
   ),
   broadcast(Args, [H | T]),
   Term =.. [Op, H | T],
   C = H.empty(H.shape(), [range(Range), dtype(FinalDType)]).push_op(Term).
% where(C, A, B) is A where C holds, else B: C is read as a boolean.
push(where(C0, A, B), D) :-
   C = C0.as(boolean),
   (  dicts_same_value_for_key([C, A, B], device, _)
   -> true
   ;  type_error(device, [C, A, B])
   ),
   broadcast_dtype(A.dtype, B.dtype, DType),
   % an element of D is one of A or B
   Range::real,
   { Range >= min(A.range, B.range), Range =< max(A.range, B.range) },
   broadcast([C, A, B], [C1, A1, B1]),
   D = A1.empty(A1.shape(), [range(Range), dtype(DType)]).push_op(where(C1, A1, B1)).
push(solve(A, B), X) :-
   (  dicts_same_value_for_key([A, B], device, _)
   -> true
   ;  domain_error(device, [A, B])
   ),
   (  [N, N] = A.shape()
   -> { N * A.range * Range == B.range }
   ;  domain_error(square, A.shape())
   ),
   X = A.empty(B.shape(), [range(Range), dtype(float)]).push_op(solve(A, B)).
dicts_same_value_for_key(List, Key, Value) :-
   maplist({Value, Key}/[Dict]>>get_dict(Key, Dict, Value), List).

broadcast(In, Out) :-
   maplist(view, In, InViews),
   broadcast_views(InViews, OutViews),
   maplist(replace_view, OutViews, In, Out).

:- table broadcast_views/2.

broadcast_views(In, Out) :-
   foldl(broadcast_shape, In, [], Shape),
   maplist(view:broadcast_view(Shape), In, Out).

broadcast_shape(View, ShapeIn, ShapeOut) :-
   length(ShapeIn, N1),
   max_list([View.ndim(), N1], N),
   lpad(N, 1, View.shape, Shape),
   lpad(N, 1, ShapeIn, PaddedShapeIn),
   maplist(broadcast_shape_, Shape, PaddedShapeIn, ShapeOut).

broadcast_shape_(1, Dim, Dim) :-
   Dim #\= 1.
broadcast_shape_(Dim, 1, Dim) :-
   Dim #\= 1.
broadcast_shape_(Dim, Dim, Dim).

M.push_op(Op) := Dict :-
   post_precision(M.put([id: _Id, op: Op]), Dict).

M.op_args() := Args :-
   phrase(op_args(M.op), Args).

op_args(Array), is_dict(Array, array) ==>
   [Array].
op_args(Atom), atomic(Atom) ==>
   [].
op_args(fused(_Node, Expr)) ==>
   op_args(Expr).
op_args(reindex(_Via, Expr)) ==>
   op_args(Expr).
op_args(Op) ==>
   { compound_name_arguments(Op, _, Args) },
   sequence(op_args, Args).


% High level Ops
% ==============
M.reduce(Axes, Op, KeepDim) := Dict :-
   must_be(list, Axes),
   must_be(oneof([+, <]), Op),
   M1 = M.push(reduce(Op, Axes)),
   (  KeepDim
   -> M1 = Dict
   ;  Dict = M1.squeeze(Axes)
   ).

M.sum() := Dict :-
   numlist(0, M.ndim0(), Axes),
   Dict = M.sum(Axes).
M.sum(Axes) := Dict :-
   Dict = M.sum(Axes, false).
M.sum(Axes, KeepDim) := Dict :-
   Dict = M.reduce(Axes, +, KeepDim).

M.max() := Dict :-
   numlist(0, M.ndim0(), Axes),
   Dict = M.max(Axes).
M.max(Axes) := Dict :-
   Dict = M.max(Axes, false).
M.max(Axes, KeepDim) := Dict :-
   Dict = M.reduce(Axes, <, KeepDim).

M.cumalu(Axis, Op) := Dict :-
   M1 = M.swapaxes(M.ndim0(), Axis),
   length(Padding, M1.ndim()),
   last(M1.shape(), Dim),
   Dim1 #= Dim - 1,
   once(append(ZeroPadding, [Dim1-0], Padding)),
   maplist(=(0-0), ZeroPadding),
   identity(Op, Identity),
   M2 = M1.pad(Padding, [constant(Identity)]),
   M3 = M2.pool([Dim]),
   M4 = M3.reduce([M3.ndim0()], Op, false),
   M5 = M4.swapaxes(Axis, M.ndim0()),
   Dict = M5.
M.cumsum(Axis) := Dict :-
   Dict = M.cumalu(Axis, +).

identity(+, 0).
identity(*, 1).
identity(<, -inf).

M.contiguous() := Dict :-
   (  M.is_contiguous()
   -> Dict = M
   ;  Dict = M.push(contiguous)
   ).

M.to(Device) := Dict :-
   (  M.device = Device
   -> Dict = M
   ;  once(Dict = M.to(M.device, Device))
   ).

M.as(DType) := Dict :-
   MDType = M.dtype,
   (  DType == MDType
   -> Dict = M
   ;  DType == boolean
   -> Dict @= (M =\= 0)
   ;  Op =.. [DType, M],
      debug(as, "~p", [Op]),
      push(Op, Dict)
   ).

'@='(Left, Right) :-
   eval_(Right, Left).
eval_(A<B, C) =>
   eval_(A, A1),
   eval_(B, B1),
   push(A1<B1, C).
eval_(A>B, C) =>
   eval_(B<A, C).
% Derived comparisons only ever hold 0 or 1, but interval arithmetic on their
% sub-expressions cannot see that, e.g. (A<B)+(A>B) gets the range [0, 2].
eval_(A=<B, C) =>
   eval_(-(A>B) + 1, C1),
   C1.range::real(0, 1),
   C = C1.put(dtype, boolean).
eval_(A>=B, C) =>
   eval_(-(A<B) + 1, C1),
   C1.range::real(0, 1),
   C = C1.put(dtype, boolean).
eval_(A=\=B, C) =>
   eval_((A<B)+(A>B), C1),
   C1.range::real(0, 1),
   C = C1.put(dtype, boolean).
eval_(A=:=B, C) =>
   eval_(-(A=\=B)+1, C1),
   C1.range::real(0, 1),
   C = C1.put(dtype, boolean).
eval_(A+B, C) =>
   eval_(A, A1),
   eval_(B, B1),
   push(A1+B1, C).
eval_(-A, C) =>
   eval_(-1*A, C).
eval_(A-B, C) =>
   eval_(A + (-1*B), C).
eval_(A*B, C) =>
   eval_(A, A1),
   eval_(B, B1),
   push(A1*B1, C).
eval_(sin(A), C) =>
   eval_(A, A1),
   push(sin(A1), C).
eval_(cos(A), C) =>
   Pi2 is pi/2,
   eval_(sin(Pi2 - A), C).
eval_(log(A), C) =>
   eval_(A, A1),
   push(log(A1), C).
eval_(sqrt(A), C) =>
   eval_(A, A1),
   push(sqrt(A1), C).
eval_(where(Cond, A, B), C) =>
   eval_(Cond, Cond1),
   eval_(A, A1),
   eval_(B, B1),
   push(where(Cond1, A1, B1), C).
eval_(A @ B, C) =>
    eval_(A, A1),
    eval_(B, B1),
    (  A1.ndim() > 1, B1.ndim() > 1
    -> nth1(A1.ndim(), Shape1, 1, A1.shape()),
       nth1(B1.ndim0(), Shape2, 1, B1.shape()),
       SwapAxis = B1.ndim0()
    ;  A1.ndim() == 1, B1.ndim() > 1
    -> SwapAxis is B1.ndim() - 2,
       Shape1 = A1.shape(),
       Shape2 = B1.shape()
    ;  SwapAxis = 0,
       Shape1 = A1.shape(),
       Shape2 = B1.shape()
    ),
    A3 = A1.reshape(Shape1),
    B2 = B1.reshape(Shape2), B3 = B2.swapaxes(B2.ndim0(), SwapAxis),
    eval_(A3 * B3, C1),
    C = C1.sum([C1.ndim0()]).
eval_(solve(A, B), X) =>
   eval_(A, A1),
   eval_(B, B1),
   push(solve(A1.contiguous(), B1.contiguous()), X).
eval_(A, R), is_dict(A, array) =>
   A = R.
eval_(A, R), number(A) =>
   R = array{}.full([], A, [device(_)]).

% Properties
% ==========
M.view() := View :-
   M.views = [View | _].

M.size() := Size :-
   Size = M.view().size().

M.shape() := Shape :-
   Shape = M.view().shape.

M.ndim() := NDim :-
   NDim = M.view().ndim().

M.ndim1() := NDim :-
   NDim #= max(1, M.ndim()).
M.ndim0() := NDim :-
   NDim #= max(0, M.ndim() - 1).

M.is_contiguous() := Res :-
   maplist(view:is_contiguous, M.views, [H | T]),
   foldl(mkconj, T, H, Res).

% The elements of a contiguous M are the M.size() elements of its buffer
% from the offset of its element 0, through all its views. An empty M reads
% nothing: its offset may lie outside the buffer.
M.data_offset() := Offset :-
   data_offset(M, M.size(), Offset).

data_offset(_, 0, Offset) =>
   Offset = 0.
data_offset(M, Size, Offset) =>
   length(Zeros, M.ndim()),
   maplist(=(0), Zeros),
   IndexExpr-_ = M.index_expr(Zeros),
   Offset is IndexExpr,
   check_in_buffer(Offset, Size, M.datasize).

check_in_buffer(Offset, Size, DataSize), Offset >= 0, Offset + Size =< DataSize =>
   true.
check_in_buffer(Offset, Size, DataSize) =>
   domain_error(in_buffer_of_size(DataSize), slice(Offset, Size)).

% Runtime
% =======

M.realize() := Dict :-
   Dict = M.realize([]).
% Options: precision(T) guarantees an error of at most T on M, choosing the
% cheapest float formats that keep it.
M.realize(Options) := M :-
   realize_array(M, Options).

% Already realized: its inputs may only have lived in the buffer pool.
realize_array(M, _), get_dict(data, M, Data), nonvar(Data) =>
   true.
realize_array(M, Options) =>
   option(precision(Tolerance), Options, inf),
   create_schedule([M], Tolerance, Schedule),  % toposort of graph
   maplist(compile, Schedule, CompiledSchedule), % generate device specific code 
   allocate_schedule(Schedule),
   run_schedule(CompiledSchedule).

% Compilation
% ============
M.compile() := Dict :-
   compile_array(M, Dict).

% A realized array is an input: its kernel already ran.
compile_array(M, Dict), get_dict(data, M, Data), nonvar(Data) =>
   Dict = M.put(kernel, true).
compile_array(M, Dict) =>
   once(Dict = M.compile(M.device, M.op)).
   % format("~p~n", [Dict.kernel]).

create_schedule(Arrays, NewSchedule) :-
   create_schedule(Arrays, inf, NewSchedule).
create_schedule(Arrays, Tolerance, NewSchedule) :-
   graph_schedule(Arrays, Schedule0),
   fuse(Arrays, Schedule0, Schedule),
   % pool offsets need each array's dtype size
   choose_formats(Schedule, Arrays, Tolerance),
   allocation_scheme(Arrays, Schedule, NewSchedule).

% graph_schedule(+Arrays, -Schedule)
% Schedule holds Arrays and the arrays they depend on, each once and after
% the arrays its op reads. A realized array depends on nothing.
% An array is visited once, by its id: arrays share their inputs, so a walk
% of the ops as a tree would be exponential in the depth of the sharing.
graph_schedule(Arrays, Schedule) :-
   rb_new(Visited),
   phrase(schedule_arrays(Arrays, Visited, _), Schedule).

schedule_arrays([], Visited0, Visited) ==>
   { Visited = Visited0 }.
schedule_arrays([Array | Arrays], Visited0, Visited) ==>
   schedule_array(Array, Visited0, Visited1),
   schedule_arrays(Arrays, Visited1, Visited).

schedule_array(Array, Visited0, Visited),
      get_dict(id, Array, Id), rb_lookup(Id, _, Visited0) ==>
   { Visited = Visited0 }.
schedule_array(Array, Visited0, Visited),
      get_dict(data, Array, Data), nonvar(Data) ==>
   { rb_insert_new(Visited0, Array.id, true, Visited) },
   [Array].
schedule_array(Array, Visited0, Visited) ==>
   {  rb_insert_new(Visited0, Array.id, true, Visited1),
      phrase(op_args(Array.op), Inputs)
   },
   schedule_arrays(Inputs, Visited1, Visited),
   [Array].

% Allocation
% ==========
allocation_scheme(Outputs, Schedule, NewSchedule) :-
   maplist(get_dict(data), Outputs, OutputDatas),
   sort(OutputDatas, UniqueOutputDatas),
   maplist([D, (exclude-D)-_]>>true, UniqueOutputDatas, ExcludePairs),
   ord_list_to_rbtree(ExcludePairs, T1),
   schedule_lifetime(Schedule, T1, T2, 0),
   apply_minimalloc(T2, Schedule, NewSchedule).

apply_minimalloc(T, Schedule, NewSchedule) :-
   rb_keys(T, Keys),
   convlist([start-D, D]>>true, Keys, Datas),
   maplist(make_buffer(T), Datas, DeviceBufferPairs),
   keysort(DeviceBufferPairs, SortedBuffers),
   group_pairs_by_key(SortedBuffers, GroupedBufferPairs),
   foldl(apply_device_minimalloc, GroupedBufferPairs, T, T1),
   maplist(update_schedule(T1), Schedule, NewSchedule).

apply_device_minimalloc(Device-Buffers, T1, T) :-
   minimalloc(Buffers, [heuristics([wat])]),
   print_term(Buffers, []), nl,
   foldl(buffer_size, Buffers, 0, BufferSize),
   rb_insert_new(T1, Device, _Buffer-BufferSize, T2),
   foldl(insert_offset, Buffers, T2, T).

insert_offset(buffer(Buffer, _, _, _, Offset), T1, T2) :-
   rb_insert_new(T1, offset-Buffer, Offset, T2).

buffer_size(buffer(_, _, _, Size, Offset), BufferSize, MaxSize) :-
   MaxSize is max((Size+Offset), BufferSize).

M.offset(Offset, Options) := Dict :-
   option(data(Data), Options, M.data),
   option(datasize(DataSize), Options, M.datasize),
   reverse(M.views, [View | Views]),
   NewOffset is View.offset + Offset,
   reverse([View.put(offset, NewOffset) | Views], OffsetViews),
   Dict = M.put([data=Data, datasize=DataSize, views=OffsetViews]).

update_schedule(T, Array, NewArray) :-
   update_op(T, Array.op, NewOp),
   update_array(T, Array.put(op, NewOp), NewArray).
update_array(T, Array, NewArray) :-
   (  rb_lookup(offset-Array.data, ByteOffset, T)
   -> rb_lookup(Array.device, Buffer-BufferSize, T),
      Size is BufferSize // Array.dtype_size(),
      Offset is ByteOffset // Array.dtype_size(),
      NewArray = Array.offset(Offset, [data(Buffer), datasize(Size)])
   ;  NewArray = Array
   ).

update_op(T, Array, NewArray), is_dict(Array, array) =>
   update_array(T, Array, NewArray).
update_op(_, Atom, R), atomic(Atom) =>
   R = Atom.
update_op(T, Op, NewOp), compound_name_arguments(Op, Name, Args) =>
   maplist(update_op(T), Args, NewArgs),
   compound_name_arguments(NewOp, Name, NewArgs).

make_buffer(T, Data, Device-buffer(Data, Start, End, Size, _)) :-
   rb_lookup(start-Data, Device-Start-DataSize, T),
   rb_lookup(end-Data, End, T),
   Size is integer(ceil(DataSize / 8) * 8).

schedule_lifetime([], T, T, _).
schedule_lifetime([Array | L], T1, T, I) :-
   I1 is I + 1,
   Data = Array.data,
   % exclude output data and already allocated data
   (  (rb_lookup(exclude-Data, _, T1) ; nonvar(Data))
   -> T3 = T1
   ;  (  rb_insert_new(T1, start-Data, Array.device-I-Array.data_byte_size(), T2)
      -> true
      ;  T2 = T1
      ),
      rb_insert(T2, end-Data, I1, T3)
   ),
   foldl(insert_end(I1), Array.op_args(), T3, T4),
   schedule_lifetime(L, T4, T, I1).
insert_end(I, Arg, T1, T2) :-
   Data = Arg.data,
   (  (rb_lookup(exclude-Data, _, T1) ; nonvar(Data))
   -> T2 = T1
   ;  rb_insert(T1, end-Data, I, T2)
   ).

allocate_schedule(Schedule) :-
   maplist(allocate, Schedule).

allocate(M) :-
   (  var(M.data)
   -> allocate(M.device, M)
   ;  true
   ).

% :- det(run_schedule/1).

run_schedule(Schedule) :-
   maplist(run_scheduleitem, Schedule).

run_scheduleitem(M) :-
   call(M.kernel).

% Helpers
% =======
M.push_view(View) := Dict :-
   Dict = M.push(view([View | M.views])).

M.pop_view(View) := Dict :-
   M.views = [View | Views],
   Dict = M.push(view(Views)).

M.replace_view(Old, New) := Dict :-
   Dict = M.pop_view(Old).push_view(New).

M.replace_view(View) := Dict :-
   Dict = M.replace_view(_, View).

M.index_expr(Index) := IndexExpr-ValidExpr :-
   M.views = [View | Views],
   foldl([V, Valid, FlatIn, FlatOut]>>(
         view:reverse_index_expr(FlatIn, V, Index_),
         view:valid_expr(Index_, V, Valid),
         view:index_expr(Index_, V, FlatOut)
      ), Views, Valids, View.index_expr(Index), IndexExpr),
   foldl(mkconj, Valids, View.valid_expr(Index), ValidExpr).

skip_view(view(M), Op) =>
   skip_view(M.op, Op).
skip_view(Op, R) =>
   R = Op.

% DTypes
% ======
:- table common_dtype/4.

common_dtype(Device, A, B, C) :-
   common_dtype_(Device, A, B, C).
common_dtype(Device, A, B, C) :-
   common_dtype_(Device, B, A, C).

:- table common_dtype_/4.
common_dtype_(_Device, A, A, A).
common_dtype_(Device, A, B, C) :-
   broadcast_dtype(Device, A, A1),
   common_dtype_(Device, A1, B, C).

broadcast_dtypes(Device, [H | DTypes], DType) :-
   foldl(common_dtype(Device), DTypes, H, DType).

get_dtype(X, R) :-
   (  X == 0
   -> R = boolean
   ;  X == 1
   -> R = boolean
   ;  integer(X)
   -> R = integer
   ;  float(X)
   -> R = float
   ;  domain_error([boolean, integer, float], X)
   ).
broadcast_dtype(boolean, boolean, boolean).
broadcast_dtype(integer, boolean, integer).
broadcast_dtype(boolean, integer, integer).
broadcast_dtype(integer, integer, integer).
broadcast_dtype(float, boolean, float).
broadcast_dtype(boolean, float, float).
broadcast_dtype(float, integer, float).
broadcast_dtype(integer, float, float).
broadcast_dtype(float, float, float).

cast(boolean, 0, Result) => Result = 0.
cast(boolean, _, Result) => Result = 1.
cast(DType, Value, Result) =>
   Expr =.. [DType, Value],
   Result is Expr.

range_min_max(Number, Min, Max), number(Number) =>
   Min = Number,
   Max = Number.
range_min_max(Range, Min, Max), clpBNR:domain(Range, Domain) =>
   (  Domain == boolean
   -> Min = 0, Max = 1
   ;  Domain =.. [_, Min, Max]
   ).

% The hardware dtype, bound once when the array gets a buffer.
M.dtype() := DType :-
   get_dict(format, M, Format),
   format_dtype(Format, DType).

format_dtype(Format, DType), atom(Format) =>
   DType = Format.
format_dtype(Format, _) =>
   instantiation_error(Format).

bind_default_format(M), get_dict(format, M, Format), nonvar(Format) =>
   true.
bind_default_format(M) =>
   default_format(M.device, M, Format),
   M.format = Format.

M.dtype_size() := Size :-
   Size = M.dtype_size(M.device).
M.data_byte_size() := Size :-
   Size is M.datasize * M.dtype_size().

:- begin_tests(array_reshape).

test('reshape that can be merged replaces the view') :-
  % Create a contiguous array.
  A = array{}.empty([2,3,4]),
  % Reshape it. view{}.reshape() can handle this.
  B = A.reshape([6,4]),
  % array{}.reshape() should replace the view, not add one.
  length(B.views, 1),
  B.view().shape == [6,4].

test('reshape that cannot be merged adds a new view') :-
  % Create a non-contiguous view that view{}.reshape() cannot handle.
  StartView = view{}.from_shape([3,2,4]).put(strides, [4,12,1]),
  A = array{}.empty([24]).replace_view(StartView),
  % Reshape it. The total size is the same.
  B = A.reshape([6,4]),
  % Since view{}.reshape() fails, array{}.reshape() must add a new view.
  length(B.views, 2),
  B.views = [NewView, StartView],
  NewView == view{}.from_shape([6,4]).

test('a reshape of unknown dims constrains nothing', [timeout(10)]) :-
  W in 1..10,
  W4 #= W*4,
  View = view{shape:[4,W], strides:[1,W], offset:0, mask:[0-4, 0-W]},
  A = array{}.empty([4, W]).replace_view(View),
  B = A.reshape([W4]),
  fd_dom(W, Dom),
  Dom == 1..10,
  array{views: Views} :< B,
  length(Views, 2).

test('a reshape of integers merges when it can', [timeout(10)]) :-
  forall(member(W-N, [1-1, 3-2]),
         (  View = view{shape:[4,W], strides:[1,W], offset:0, mask:[0-4, 0-W]},
            A = array{}.empty([4, W]).replace_view(View),
            W4 is W*4,
            B = A.reshape([W4]),
            array{views: Views} :< B,
            length(Views, N)
         )).

test('reshape with mismatched size fails', [throws(error(domain_error(_,_),_))]) :-
  A = array{}.empty([2,3]),
  % New shape has size 9, original has size 6.
  _ = A.reshape([3,3]).

:- end_tests(array_reshape).

:- begin_tests(index_expr).

test('contiguous') :-
    A = array{}.empty([4, 5]),
    IndexExpr-ValidExpr = A.index_expr([1, 2]),
    7 is IndexExpr,
    ValidExpr.

test('offset') :-
    V = view{}.from_shape([4, 5]).put(offset, 10),
    A = array{}.default().push_view(V),
    IndexExpr-ValidExpr = A.index_expr([1, 2]),
    17 is IndexExpr,
    ValidExpr.

test('sliced') :-
    % A 3x4 slice from a 10x10 array, starting at (2,3)
    V = view{shape:[3,4], strides:[10,1], mask:[0-3,0-4], offset:23},
    A = array{}.default().push_view(V),
    % logical coordinate (1,1) in the 3x4 slice
    % physical flat index should be for (2+1, 3+1) = (3,4) in 10x10 array
    % which is 3*10 + 4 = 34
    IndexExpr-ValidExpr = A.index_expr([1, 1]),
    34 is IndexExpr,
    ValidExpr.

test('transposed') :-
    % A 10x20 array, transposed to 20x10
    V = view{shape:[20,10], strides:[1,20], mask:[0-20,0-10], offset:0},
    A = array{}.default().push_view(V),
    % logical coordinate (2,1) in 20x10 array
    % this corresponds to (1,2) in 10x20 array
    % physical flat index is 1*20 + 2 = 22
    IndexExpr-ValidExpr = A.index_expr([2, 1]),
    22 is IndexExpr,
    ValidExpr.

test('stacked views') :-
    % A permuted array that is reshaped, adding a view
    V_permute = view{shape:[3,2,4], strides:[4,12,1], offset:0, mask:[0-3,0-2,0-4]},
    V_reshape = view{}.from_shape([6,4]), % logical view
    A = array{}.default().put(views, [V_reshape, V_permute]),
    % logical coordinate (1,3) in 6x4 array
    % -> logical flat index 7 for V_permute
    % -> logical coordinate (0,1,3) for V_permute (shape [3,2,4])
    % -> physical index is 0*4 + 1*12 + 3*1 = 15
    IndexExpr-ValidExpr = A.index_expr([1,3]),
    15 is IndexExpr,
    ValidExpr.

test('three stacked views') :-
    V_phys = view{}.from_shape([100]),
    V_transpose = view{shape:[10,10], strides:[1,10], mask:[0-10,0-10], offset:0},
    V_reshape = view{}.from_shape([2,5,10]),
    A = array{}.default().put(views, [V_reshape, V_transpose, V_phys]),
    % logical coordinate (0,2,5) in [2,5,10] array
    % -> logical flat index 25 for V_transpose
    % -> logical coordinate (2,5) for V_transpose (shape [10,10])
    % -> physical flat index 52 from V_transpose (strides [1,10])
    % -> logical flat index 52 for V_phys
    % -> physical flat index 52 from V_phys (contiguous)
    IndexExpr-ValidExpr = A.index_expr([0,2,5]),
    52 is IndexExpr,
    ValidExpr.

:- end_tests(index_expr).

:- begin_tests(array_empty).

test('create empty array') :-
  A = array{}.empty([2,3], [dtype(float), device(prolog)]),
  A.shape() == [2,3],
  A.dtype == float,
  A.device == prolog,
  A.op == true,
  length(A.views, 1),
  A.view().shape == [2,3].

:- end_tests(array_empty).

:- begin_tests(array_tolist).

test('4x4') :-
    A = array{}.empty([4, 4]),
    List = A.tolist(),
    length(List, 4),
    maplist([L]>>length(L, 4), List).

:- end_tests(array_tolist).

:- begin_tests(array_realize).

% Reading a realized array must not compute it again: rand would change it.
test('a realized input keeps its values', [forall(member(D, [prolog, c]))]) :-
    A0 = array{}.rand([3], [device(D)]),
    A = A0.realize(),
    L1 = A.tolist(),
    C = A.sum(),
    _ = C.realize(),
    L2 = A.tolist(),
    L1 == L2.

:- end_tests(array_realize).

:- begin_tests(array_shrink).

shrunk_padding(D, Shrink, Expected) :-
    A = array{}.fromlist([1.0, 2.0], [device(D)]),
    B = A.pad([1-1]).shrink([Shrink]),
    List = B.tolist(),
    List == Expected.

test('a shrink of a padded array reads the padding as 0',
     [forall(member(D, [prolog, c])), timeout(30)]) :-
    shrunk_padding(D, 0-2, [0.0, 1.0]),
    shrunk_padding(D, 2-4, [2.0, 0.0]),
    shrunk_padding(D, 1-3, [1.0, 2.0]),
    shrunk_padding(D, 3-4, [0.0]).

:- end_tests(array_shrink).

:- begin_tests(array_slice).

slice(Base, Shrink, Slice) :-
    Slice = Base.shrink(Shrink).

matrix(D, M) :-
    M = array{}.fromlist([[1.0, 2.0, 3.0], [4.0, 5.0, 6.0]], [device(D)]).

test('a slice of a buffer reads its elements',
     [forall(member(D, [prolog, c])), timeout(30)]) :-
    A = array{}.fromlist([1.0, 2.0, 3.0], [device(D)]),
    slice(A, [0-2], Prefix),
    Prefix.tolist() == [1.0, 2.0],
    slice(A, [1-3], Suffix),
    Suffix.tolist() == [2.0, 3.0],
    matrix(D, M),
    slice(M, [1-2, 0-3], Row),
    Row.tolist() == [[4.0, 5.0, 6.0]].

test('contiguous keeps a slice', [timeout(30)]) :-
    matrix(prolog, M),
    slice(M, [1-2, 0-3], Row),
    C = Row.contiguous(),
    array{op: Op} :< C,
    Op = view(_).

test('contiguous copies a column',
     [forall(member(D, [prolog, c])), timeout(30)]) :-
    matrix(D, M),
    slice(M, [0-2, 1-2], Column),
    C = Column.contiguous(),
    array{op: Op} :< C,
    Op = contiguous(_),
    Column.tolist() == [[2.0], [5.0]].

test('a slice is transferred alone',
     [forall(member(From-To, [prolog-c, c-prolog])), timeout(30)]) :-
    A = array{}.fromlist([1.0, 2.0, 3.0], [device(From)]),
    slice(A, [1-3], Suffix),
    B = Suffix.to(To),
    array{datasize: Size} :< B,
    Size == 2,
    B.tolist() == [2.0, 3.0].

test('an empty slice of padding reads nothing',
     [forall(member(From-To, [prolog-c, c-prolog])), timeout(30)]) :-
    A = array{}.fromlist([1.0, 2.0], [device(From)]),
    Empty = A.pad([1-0]).shrink([0-0]),
    Empty.tolist() == [],
    Empty.to(To).tolist() == [].

test('a view past its buffer fails loudly',
     [throws(error(domain_error(in_buffer_of_size(2), slice(1, 2)), _)),
      timeout(30)]) :-
    A = array{}.fromlist([1.0, 2.0]),
    View = view{shape: [2], strides: [1], mask: [0-2], offset: 1},
    B = A.replace_view(View),
    _ = B.tolist().

test('solve reads a matrix from an offset', [timeout(30)]) :-
    Big = array{}.fromlist([[9.0, 9.0], [2.0, 0.0], [0.0, 4.0]]),
    A = Big.shrink([1-3, 0-2]),
    B = array{}.fromlist([2.0, 8.0]),
    X @= solve(A, B),
    X.tolist() == [1.0, 2.0].

:- end_tests(array_slice).

:- begin_tests(array_flip_stride).

% The reference: flip, then stride, nested lists dim by dim.
at_depth(0, Goal, L, R) :-
    call(Goal, L, R).
at_depth(D, Goal, L, R) :-
    D > 0,
    D1 is D - 1,
    maplist(at_depth(D1, Goal), L, R).

flip_list(0, L, L).
flip_list(1, L, R) :-
    reverse(L, R).

every(K, L, R) :-
    findall(X, (nth0(I, L, X), I mod K =:= 0), R).

reference(Flags, Steps, L0, L) :-
    length(Flags, N),
    Last is N - 1,
    numlist(0, Last, Axes),
    foldl([Axis, F, A, B]>>at_depth(Axis, flip_list(F), A, B), Axes, Flags, L0, L1),
    foldl([Axis, K, A, B]>>at_depth(Axis, every(K), A, B), Axes, Steps, L1, L).

nested([], [X | Xs], X, Xs).
nested([Dim | Shape], Xs0, L, Xs) :-
    length(L, Dim),
    foldl([E, A, B]>>nested(Shape, A, E, B), L, Xs0, Xs).

test('flip and stride read as the reference',
     [forall(member(D, [prolog, c])), timeout(60)]) :-
    set_random(seed(7)),
    forall(between(1, 12, _),
           (  random_between(1, 3, NDim),
              length(Shape, NDim),
              maplist(random_between(1, 4), Shape),
              length(Flags, NDim),
              maplist(random_between(0, 1), Flags),
              length(Steps, NDim),
              maplist(random_between(1, 3), Steps),
              foldl([Dim, S0, S]>>(S is S0*Dim), Shape, 1, Size),
              numlist(1, Size, Is),
              maplist([I, X]>>(X is float(I)), Is, Xs),
              nested(Shape, Xs, L0, []),
              A = array{}.fromlist(L0, [device(D)]),
              B = A.flip(Flags).stride(Steps),
              reference(Flags, Steps, L0, Expected),
              B.tolist() == Expected
           )).

test('a flip reads the padding flipped',
     [forall(member(D, [prolog, c])), timeout(30)]) :-
    A = array{}.fromlist([1.0, 2.0], [device(D)]),
    B = A.pad([1-0]).flip([1]),
    B.tolist() == [2.0, 1.0, 0.0].

test('a stride skips the padding',
     [forall(member(D, [prolog, c])), timeout(30)]) :-
    A = array{}.fromlist([1.0, 2.0, 3.0], [device(D)]),
    B = A.pad([1-1]).stride([2]),
    B.tolist() == [0.0, 2.0, 0.0].

test('a flipped array reshapes into one view',
     [forall(member(D, [prolog, c])), timeout(30)]) :-
    A = array{}.fromlist([[1.0, 2.0, 3.0], [4.0, 5.0, 6.0]], [device(D)]),
    B = A.flip([1, 1]).reshape([6]),
    array{views: Views} :< B,
    length(Views, 1),
    B.tolist() == [6.0, 5.0, 4.0, 3.0, 2.0, 1.0].

test('a flipped array is copied by contiguous', [timeout(30)]) :-
    A = array{}.fromlist([1.0, 2.0, 3.0]),
    C = A.flip([1]).contiguous(),
    array{op: Op} :< C,
    Op = contiguous(_).

:- end_tests(array_flip_stride).

:- begin_tests(array_index).

devices(D) :-
    member(D, [prolog, c]).

test('single element indexing', [forall(devices(D)), timeout(30)]) :-
    X = array{}.arange(10, [device(D)]),
    X.index([2]).tolist() == 2,
    X.index([-2]).tolist() == 8,
    Y = X.reshape([2, 5]),
    Y.index([1, 3]).tolist() == 8,
    Y.index([1, -1]).tolist() == 9,
    Y.index([0]).tolist() == [0, 1, 2, 3, 4],
    Y.index([0]).index([2]).tolist() == 2.

test('slicing and striding', [forall(devices(D)), timeout(30)]) :-
    X = array{}.arange(10, [device(D)]),
    X.index([1:7:2]).tolist() == [1, 3, 5],
    X.index([-2:10]).tolist() == [8, 9],
    X.index([-3:3: -1]).tolist() == [7, 6, 5, 4],
    X.index([5:sup]).tolist() == [5, 6, 7, 8, 9],
    X.index([sup:inf: -2]).tolist() == [9, 7, 5, 3, 1],
    X.index([5:2]).tolist() == [],
    X.index([2:5: -1]).tolist() == [].

test('slicing a dim of 3 dims', [forall(devices(D)), timeout(30)]) :-
    X = array{}.fromlist([[[1], [2], [3]], [[4], [5], [6]]], [device(D)]),
    X.index([1:2]).tolist() == [[[4], [5], [6]]].

test('whole dims and new dims', [forall(devices(D)), timeout(30)]) :-
    Y = array{}.arange(10, [device(D)]).reshape([2, 5]),
    Y.index([:, 1]).tolist() == [1, 6],
    Y.index([new, 0]).tolist() == [[0, 1, 2, 3, 4]],
    % as numpy, the dims missing from the index come after the new dim
    Y.index([0, new]).tolist() == [[0, 1, 2, 3, 4]],
    Y.index([0, :, new]).tolist() == [[0], [1], [2], [3], [4]],
    Y.index([1, sup:inf: -1]).tolist() == [9, 8, 7, 6, 5].

test('an index out of its dim fails', [timeout(30)]) :-
    X = array{}.arange(10),
    \+ _ = X.index([10]),
    \+ _ = X.index([-11]),
    \+ _ = X.index([0, 0]).

test('an index reads the padding', [forall(devices(D)), timeout(30)]) :-
    A = array{}.fromlist([1.0, 2.0], [device(D)]).pad([1-1]),
    A.index([0]).tolist() == 0.0,
    A.index([1:3]).tolist() == [1.0, 2.0],
    A.index([sup:inf: -1]).tolist() == [0.0, 2.0, 1.0, 0.0],
    A.index([0:sup:2]).tolist() == [0.0, 2.0].

test('an unknown index reads every row once labelled', [timeout(30)]) :-
    Y = array{}.arange(10).reshape([2, 5]),
    B = Y.index([I]),
    findall(I-L, (label([I]), L = B.tolist()), Rows),
    Rows == [-2-[0, 1, 2, 3, 4], -1-[5, 6, 7, 8, 9],
             0-[0, 1, 2, 3, 4], 1-[5, 6, 7, 8, 9]].

test('an index from the end of an unknown dim', [timeout(30)]) :-
    W in 1..10,
    A = array{}.empty([W]),
    B = A.index([-1]),
    W = 5,
    B.data_offset() == 4.

test('index finds the step giving a shape', [timeout(30)]) :-
    A = array{}.empty([8]),
    findall(K,
            (  K in 1..8,
               B = A.index([0:sup:K]),
               B.shape() = [3],
               label([K])
            ),
            Ks),
    Ks == [3].

test('an index item of another syntax fails loudly',
     [throws(error(type_error(index_item, foo), _)), timeout(30)]) :-
    X = array{}.arange(10),
    _ = X.index([foo]).

:- end_tests(array_index).

:- begin_tests(array_gather).

devices(D) :-
    member(D, [prolog, c]).

% A float64 array on Device holding Values, which may hold NaN: its range
% is the given one.
nan_array(Device, Values, Min, Max, A) :-
    length(Values, N),
    Data =.. [data | Values],
    buffer:buffer_from_data(Buffer, float64, N, Data),
    Range::real(Min, Max),
    A0 = array{}.empty([N], [device(c), dtype(float), data(Buffer),
                             format(float64), range(Range)]),
    A = A0.to(Device).

test('an array indexes by value', [forall(devices(D)), timeout(60)]) :-
    X = array{}.arange(10, 1, -1, [device(D)]),
    X.index([[3, 3, 1, 8]]).tolist() == [7, 7, 9, 2],
    X.index([[3, 3, -3, 8]]).tolist() == [7, 7, 4, 2],
    Y = array{}.fromlist([[1, 2], [3, 4], [5, 6]], [device(D)]),
    Y.index([[1, -1]]).tolist() == [[3, 4], [5, 6]],
    Y.index([[0, 1, 2], [0, 1, 0]]).tolist() == [1, 4, 5].

test('index arrays broadcast together', [forall(devices(D)), timeout(60)]) :-
    X = array{}.arange(35, [device(D)]).reshape([5, 7]),
    X.index([[0, 2, 4], [0, 1, 2]]).tolist() == [0, 15, 30],
    X.index([[0, 2, 4], 1]).tolist() == [1, 15, 29],
    X.index([[0, 2, 4]]).tolist() == [[0, 1, 2, 3, 4, 5, 6],
                                      [14, 15, 16, 17, 18, 19, 20],
                                      [28, 29, 30, 31, 32, 33, 34]],
    Z = array{}.fromlist([[0, 1, 2], [3, 4, 5], [6, 7, 8], [9, 10, 11]], [device(D)]),
    Rows = array{}.fromlist([[0, 0], [3, 3]], [device(D)]),
    Columns = array{}.fromlist([[0, 2], [0, 2]], [device(D)]),
    Z.index([Rows, Columns]).tolist() == [[0, 2], [9, 11]],
    R = array{}.fromlist([0, 3], [device(D)]),
    C = array{}.fromlist([0, 2], [device(D)]),
    Z.index([R.reshape([2, 1]), C]).tolist() == [[0, 2], [9, 11]],
    Z.index([R, C]).tolist() == [0, 11].

test('index arrays go first unless adjacent', [forall(devices(D)), timeout(60)]) :-
    W = array{}.arange(24, [device(D)]).reshape([2, 3, 4]),
    W.index([[0, 1], :, [1, 2]]).tolist() == [[1, 5, 9], [14, 18, 22]],
    W.index([:, [0, 2], [1, 3]]).tolist() == [[1, 11], [13, 23]],
    % an integer is an advanced item next to an array, as in numpy
    W.index([1, :, [0, 1]]).tolist() == [[12, 16, 20], [13, 17, 21]],
    W.index([:, 1, [0, 1]]).tolist() == [[4, 5], [16, 17]],
    W.index([[0, 1], new, [0, 1]]).tolist() == [[[0, 1, 2, 3]], [[16, 17, 18, 19]]],
    X = array{}.arange(35, [device(D)]).reshape([5, 7]),
    X.index([1:3, [0, 6]]).tolist() == [[7, 13], [14, 20]].

test('an index that may be out of its dim fails', [timeout(60)]) :-
    Y = array{}.fromlist([[1, 2], [3, 4], [5, 6]]),
    \+ _ = Y.index([[3, 4]]),
    \+ _ = Y.index([[1, 5]]),
    \+ _ = Y.index([[-4, 0]]),
    X = array{}.arange(35).reshape([5, 7]),
    \+ _ = X.index([[0, 2, 4], [0, 1]]),
    % a loose range fails too: I - I is 0, but its range is [-3, 3]
    I = array{}.fromlist([0, 3]),
    J @= I - I,
    \+ _ = Y.index([J]).

test('a computed index array', [forall(devices(D)), timeout(60)]) :-
    X = array{}.arange(10, 1, -1, [device(D)]),
    I0 = array{}.fromlist([2, 0], [device(D)]),
    I @= I0 + 1,
    X.index([I]).tolist() == [7, 9].

test('a gather never reads what it does not select',
     [forall(devices(D)), timeout(60)]) :-
    current_prolog_flag(float_undefined, Undefined),
    setup_call_cleanup(
        set_prolog_flag(float_undefined, nan),
        (  NaN is nan,
           nan_array(D, [1.0, NaN, 3.0], 1.0, 3.0, X),
           X.index([[0, 2]]).tolist() == [1.0, 3.0]
        ),
        set_prolog_flag(float_undefined, Undefined)).

test('a gather reads the padding', [forall(devices(D)), timeout(60)]) :-
    A = array{}.fromlist([1.0, 2.0], [device(D)]).pad([1-1]),
    A.index([[0, 2, 3]]).tolist() == [0.0, 2.0, 0.0].

test('a gather has the range and precision of what it selects', [timeout(60)]) :-
    numlist(1, 100, Ns),
    maplist([N, X]>>(X is 2*N), Ns, Xs),
    A = array{}.fromlist(Xs, [device(c)]),
    G = A.index([[99, 0]]),
    G.tolist() == [200, 2],
    array{format: Format} :< G,
    Format == uint8,
    maplist([N, X]>>(X is float(N)), Ns, Fs),
    F = array{}.fromlist(Fs, [precision(0.01)]),
    precision:sup_precision(F.index([[99, 0]]), P),
    P < 0.0101.

test('an index array holds integers',
     [throws(error(type_error(integer_index_array, _), _)), timeout(60)]) :-
    X = array{}.arange(10),
    F = array{}.fromlist([1.0, 2.0]),
    _ = X.index([F]).

:- end_tests(array_gather).

:- begin_tests(array_index_put).

devices(D) :-
    member(D, [prolog, c]).

test('index_put writes what index reads', [forall(devices(D)), timeout(60)]) :-
    A = array{}.fromlist([1.0, 2.0, 3.0, 4.0], [device(D)]),
    A.index_put([2], 9.0).tolist() == [1.0, 2.0, 9.0, 4.0],
    A.index_put([1:3], [7.0, 8.0]).tolist() == [1.0, 7.0, 8.0, 4.0],
    A.index_put([0:sup:2], 0).tolist() == [0.0, 2.0, 0.0, 4.0],
    A.index_put([sup:inf: -1], [10.0, 20.0, 30.0, 40.0]).tolist()
        == [40.0, 30.0, 20.0, 10.0],
    A.index_put([sup:inf: -2], [10.0, 20.0]).tolist() == [1.0, 20.0, 3.0, 10.0].

test('index_put of a dim of a matrix', [forall(devices(D)), timeout(60)]) :-
    M = array{}.fromlist([[1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12]], [device(D)]),
    M.index_put([1], [0, 0, 0, 0]).tolist()
        == [[1, 2, 3, 4], [0, 0, 0, 0], [9, 10, 11, 12]],
    M.index_put([:, 2], 0).tolist() == [[1, 2, 0, 4], [5, 6, 0, 8], [9, 10, 0, 12]],
    M.index_put([0:2, 1:3], [[7, 7], [7, 7]]).tolist()
        == [[1, 7, 7, 4], [5, 7, 7, 8], [9, 10, 11, 12]],
    M.index_put([1:3, :], [5, 6, 7, 8]).tolist()
        == [[1, 2, 3, 4], [5, 6, 7, 8], [5, 6, 7, 8]],
    M.index_put([0, new], [[20, 21, 22, 23]]).tolist()
        == [[20, 21, 22, 23], [5, 6, 7, 8], [9, 10, 11, 12]].

test('index_put writes over the padding', [forall(devices(D)), timeout(60)]) :-
    A = array{}.fromlist([1.0, 2.0], [device(D)]).pad([1-1]),
    A.index_put([0], 5.0).tolist() == [5.0, 1.0, 2.0, 0.0].

test('index_put never reads what it writes over',
     [forall(devices(D)), timeout(60)]) :-
    current_prolog_flag(float_undefined, Undefined),
    setup_call_cleanup(
        set_prolog_flag(float_undefined, nan),
        (  NaN is nan,
           Data = data(1.0, NaN, 3.0),
           buffer:buffer_from_data(Buffer, float64, 3, Data),
           Range::real(1.0, 3.0),
           A0 = array{}.empty([3], [device(c), dtype(float), data(Buffer),
                                    format(float64), range(Range)]),
           A = A0.to(D),
           A.index_put([1], 2.0).tolist() == [1.0, 2.0, 3.0]
        ),
        set_prolog_flag(float_undefined, Undefined)).

test('index_put casts its values when nothing is lost', [timeout(60)]) :-
    F = array{}.fromlist([1.0, 2.0]),
    F.index_put([0], 7).tolist() == [7.0, 2.0],
    I = array{}.fromlist([1, 2, 3]),
    I.index_put([0], 0).tolist() == [0, 2, 3],
    \+ _ = I.index_put([0], 2.5),
    Big is 2**60,
    B = array{}.fromlist([Big]),
    \+ _ = F.index_put([0], B),
    Bool = array{}.fromlist([0, 1]),
    \+ _ = Bool.index_put([0], 2).

test('index_put fails out of its array', [timeout(60)]) :-
    A = array{}.fromlist([1.0, 2.0, 3.0, 4.0]),
    \+ _ = A.index_put([4], 1.0),
    \+ _ = A.index_put([1:3], [1.0, 2.0, 3.0]),
    M = array{}.fromlist([[1, 2], [3, 4]]),
    \+ _ = M.index_put([0, new], [[5], [6]]).

test('index_put writes through index arrays', [forall(devices(D)), timeout(120)]) :-
    A = array{}.fromlist([10, 20, 30, 40], [device(D)]),
    A.index_put([[3, 0]], [7, 8]).tolist() == [8, 20, 30, 7],
    A.index_put([[1, 2]], 5).tolist() == [10, 5, 5, 40],
    A.index_put([[-1]], [9]).tolist() == [10, 20, 30, 9],
    Z = array{}.fromlist([[0, 1, 2], [3, 4, 5], [6, 7, 8], [9, 10, 11]], [device(D)]),
    Z.index_put([[0, 2], [1, 2]], [-1, -2]).tolist()
        == [[0, -1, 2], [3, 4, 5], [6, 7, -2], [9, 10, 11]],
    Z.index_put([[1, 3]], [[0, 0, 0], [1, 1, 1]]).tolist()
        == [[0, 1, 2], [0, 0, 0], [6, 7, 8], [1, 1, 1]],
    R = array{}.fromlist([0, 3], [device(D)]),
    C = array{}.fromlist([0, 2], [device(D)]),
    Z.index_put([R.reshape([2, 1]), C], [[-1, -2], [-3, -4]]).tolist()
        == [[-1, 1, -2], [3, 4, 5], [6, 7, 8], [-3, 10, -4]],
    Z.index_put([1:3, [0, 2]], [[50, 51], [52, 53]]).tolist()
        == [[0, 1, 2], [50, 4, 51], [52, 7, 53], [9, 10, 11]].

test('index_put places index arrays first unless adjacent',
     [forall(devices(D)), timeout(120)]) :-
    W = array{}.arange(24, [device(D)]).reshape([2, 3, 4]),
    B = W.index_put([[0, 1], :, [1, 2]], [[100, 101, 102], [103, 104, 105]]),
    B.tolist() == [[[0, 100, 2, 3], [4, 101, 6, 7], [8, 102, 10, 11]],
                   [[12, 13, 103, 15], [16, 17, 104, 19], [20, 21, 105, 23]]].

test('the last write of an element wins', [forall(devices(D)), timeout(120)]) :-
    A = array{}.fromlist([10, 20, 30, 40], [device(D)]),
    A.index_put([[0, 0]], [7, 8]).tolist() == [8, 20, 30, 40],
    A.index_put([[1, 2, 1]], [5, 6, 7]).tolist() == [10, 7, 6, 40].

test('index_put fails on an index that may be out of its dim', [timeout(60)]) :-
    A = array{}.fromlist([10, 20, 30, 40]),
    \+ _ = A.index_put([[4]], [1]),
    \+ _ = A.index_put([[1, -5]], [1, 2]),
    \+ _ = A.index_put([[1, 2]], [1, 2, 3]).

test('index_put through arrays has the precision of its values', [timeout(60)]) :-
    A = array{}.fromlist([1.0, 2.0, 3.0, 4.0]),
    V = array{}.fromlist([5.0, 6.0], [precision(0.01)]),
    precision:sup_precision(A.index_put([[1, 2]], V), P),
    P < 0.0101.

% pclp's patch_submatrix: a block of a covariance written back by its keys.
test('index_put patches a submatrix', [forall(devices(D)), timeout(120)]) :-
    P = array{}.fromlist([[4.0, 1.0, 0.5], [1.0, 3.0, 0.2], [0.5, 0.2, 2.0]], [device(D)]),
    Keys = array{}.fromlist([0, 2], [device(D)]),
    Sub = array{}.fromlist([[9.0, 8.0], [8.0, 7.0]], [device(D)]),
    P1 = P.index_put([Keys.reshape([2, 1]), Keys], Sub),
    P1.tolist() == [[9.0, 1.0, 8.0], [1.0, 3.0, 0.2], [8.0, 0.2, 7.0]].

test('index_put into an unknown dim', [nondet, timeout(60)]) :-
    W in 1..10,
    A = array{}.full([W], 1.0),
    B = A.index_put([-1], 5.0),
    W = 3,
    B.tolist() == [1.0, 1.0, 5.0].

:- end_tests(array_index_put).

:- begin_tests(array_where).

% A float64 array on Device holding Values, which may hold NaN.
nan_array(Device, Values, A) :-
    length(Values, N),
    Data =.. [data | Values],
    buffer:buffer_from_data(Buffer, float64, N, Data),
    A0 = array{}.empty([N], [device(c), dtype(float), data(Buffer),
                             format(float64)]),
    A = A0.to(Device).

test('where selects elementwise', [forall(member(D, [prolog, c])), timeout(30)]) :-
    A = array{}.fromlist([-2.0, 1.0, -0.5, 3.0], [device(D)]),
    C @= where(A > 0, A, 0),
    C.tolist() == [0.0, 1.0, 0.0, 3.0].

test('where never reads what it does not select',
     [forall(member(D, [prolog, c])), timeout(30)]) :-
    current_prolog_flag(float_undefined, Undefined),
    setup_call_cleanup(
        set_prolog_flag(float_undefined, nan),
        (  NaN is nan,
           nan_array(D, [1.0, NaN, 3.0], X),
           M = array{}.fromlist([1, 0, 1], [device(D)]),
           C @= where(M, X, 0),
           C.tolist() == [1.0, 0.0, 3.0]
        ),
        set_prolog_flag(float_undefined, Undefined)).

test('where reads a condition as a boolean',
     [forall(member(D, [prolog, c])), timeout(30)]) :-
    I = array{}.fromlist([0, 2, -1], [device(D)]),
    A = array{}.fromlist([1, 2, 3], [device(D)]),
    B = array{}.fromlist([7, 8, 9], [device(D)]),
    C @= where(I, A, B),
    C.tolist() == [7, 2, 3].

test('where has the dtype and the range of its operands', [timeout(30)]) :-
    A = array{}.fromlist([1, 2]),
    B = array{}.fromlist([0.5, 4.0]),
    C @= where(A > 1, A, B),
    array{dtype: DType, range: Range} :< C,
    DType == float,
    array:range_min_max(Range, Min, Max),
    Min =:= 0.5,
    Max =:= 4.0,
    T @= where(A > 1, A > 0, A < 0),
    array{dtype: TType} :< T,
    TType == boolean.

test('a wrong condition selects the other operand', [timeout(30)]) :-
    A = array{}.fromlist([1, 1]),
    B = array{}.fromlist([5, 5]),
    Exact = array{}.fromlist([1.0, -1.0]),
    C @= where(Exact > 0, A, B),
    precision:sup_precision(C, S0),
    S0 =:= 0,
    Noisy = array{}.fromlist([1.0, -1.0], [precision(0.1)]),
    E @= where(Noisy > 0, A, B),
    precision:sup_precision(E, S),
    S >= 4,
    S < 4.001.

:- end_tests(array_where).

:- begin_tests(array_squeeze).

test('a squeezed element of padding reads 0',
     [forall(member(D, [prolog, c])), timeout(30)]) :-
    A = array{}.fromlist([1.0, 2.0], [device(D)]),
    B = A.pad([1-0]).shrink([0-1]).squeeze(),
    X = B.tolist(),
    X == 0.0.

test('a squeezed row of padding reads 0',
     [forall(member(D, [prolog, c])), timeout(30)]) :-
    A = array{}.fromlist([[1.0, 2.0], [3.0, 4.0]], [device(D)]),
    P = A.pad([1-0, 0-0]),
    Row0 = P.shrink([0-1, 0-2]).squeeze([0]).tolist(),
    Row0 == [0.0, 0.0],
    Row2 = P.shrink([2-3, 0-2]).squeeze([0]).tolist(),
    Row2 == [3.0, 4.0].

test('a squeezed dim of size 1 keeps one view whatever its stride',
     [forall(member(D, [prolog, c])), timeout(30)]) :-
    A = array{}.fromlist([[1.0, 2.0], [3.0, 4.0], [5.0, 6.0]], [device(D)]),
    Row = A.transpose().shrink([1-2, 0-3]),
    B = Row.squeeze([0]),
    array{views: Views} :< B,
    length(Views, 1),
    B.tolist() == [2.0, 4.0, 6.0].

test('an expanded element of padding reads 0',
     [forall(member(D, [prolog, c])), timeout(30)]) :-
    A = array{}.fromlist([1.0, 2.0], [device(D)]),
    B = A.pad([1-0]).shrink([0-1]).expand([3]),
    List = B.tolist(),
    List == [0.0, 0.0, 0.0].

:- end_tests(array_squeeze).

:- begin_tests(array_pad).

test('the padding of a float array is a float',
     [forall(member(D, [prolog, c])), timeout(30)]) :-
    A = array{}.fromlist([1.0, 2.0], [device(D)]),
    List = A.pad([1-1]).tolist(),
    List == [0.0, 1.0, 2.0, 0.0].

test('the padding of a float constant is a float',
     [forall(member(D, [prolog, c])), timeout(30)]) :-
    A = array{}.full([2], 1.5, [device(D)]),
    List = A.pad([1-1]).tolist(),
    List == [0.0, 1.5, 1.5, 0.0].

test('the padding of an integer array is an integer',
     [forall(member(D, [prolog, c])), timeout(30)]) :-
    A = array{}.fromlist([1, 2], [device(D)]),
    List = A.pad([1-1]).tolist(),
    List == [0, 1, 2, 0].

:- end_tests(array_pad).

:- begin_tests(array_max).

% A float64 array on Device holding Values, which may hold NaN: ranges can't,
% so it starts as a C buffer, with an unbounded range.
float_array(Device, Values, A) :-
    length(Values, N),
    Data =.. [data | Values],
    buffer:buffer_from_data(Buffer, float64, N, Data),
    A0 = array{}.empty([N], [device(c), dtype(float), data(Buffer),
                             format(float64)]),
    A = A0.to(Device).

nan(X) :-
    float(X),
    float_class(X, nan).

test('a maximum over an empty axis fails loudly',
     [throws(error(domain_error(non_empty_axes, [1]), _))]) :-
    A = array{}.fromlist([[1.0, 2.0]]),
    B = A.shrink([0-1, 0-0]),
    _ = B.max([1]).

test('a maximum propagates NaN', [forall(member(D, [prolog, c]))]) :-
    current_prolog_flag(float_undefined, Undefined),
    setup_call_cleanup(set_prolog_flag(float_undefined, nan),
                       (  NaN is nan,
                          float_array(D, [1.0, NaN, 3.0], A),
                          float_array(D, [NaN, 1.0], B),
                          float_array(D, [1.0, 3.0], C),
                          nan(A.max().tolist()),
                          nan(B.max().tolist()),
                          C.max().tolist() == 3.0
                       ),
                       set_prolog_flag(float_undefined, Undefined)).

:- end_tests(array_max).

:- begin_tests(array_matmul).

test('2d @ 1d') :-
  A = array{}.fromlist([[1,2],[3,4]]),
  B = array{}.fromlist([5,6]),
  C @= A @ B,
  C.tolist() == [17, 39].

test('1d @ 1d') :-
  A = array{}.fromlist([1,2]),
  B = array{}.fromlist([3,4]),
  C @= A @ B,
  C.tolist() == 11.

test('1d @ 2d') :-
  A = array{}.fromlist([1,2]),
  B = array{}.fromlist([[3,4],[5,6]]),
  C @= A @ B,
  C.tolist() == [13, 16].

test('1d @ 3d') :-
  A = array{}.fromlist([1,2]),
  B = array{}.fromlist([[[1,2],[3,4]],[[5,6],[7,8]]]),
  C @= A @ B,
  C.tolist() == [[7,10],[19,22]].


test('2d @ 2d') :-
  A = array{}.arange(9).reshape([3, 3]),
  C @= A @ A,
  [[ 15,  18,  21],
   [ 42,  54,  66],
   [ 69,  90, 111]] = C.tolist().

test('2d @ 2d c') :-
  A = array{}.arange(9, [device(c)]).reshape([3, 3]),
  C @= A @ A,
  [[ 15,  18,  21],
   [ 42,  54,  66],
   [ 69,  90, 111]] = C.tolist().

:- end_tests(array_matmul).

:- begin_tests(array_comparison).

test('comparison op returns boolean dtype') :-
    A = array{}.fromlist([1.0, 2.0, 3.0]),
    B = array{}.fromlist([3.0, 2.0, 1.0]),
    C @= (A < B),
    C.dtype == boolean.

test('derived comparison op returns boolean dtype') :-
    A = array{}.fromlist([1.0, 2.0, 3.0]),
    B = array{}.fromlist([3.0, 2.0, 1.0]),
    C @= (A =< B),
    C.dtype == boolean.

:- end_tests(array_comparison).

:- begin_tests(c_dtype).

test('cast integer to float') :-
    A = array{}.fromlist([1, 2, 3], [device(c)]),
    C = A.as(float),
    C.tolist() == [1.0, 2.0, 3.0].

test('cast float to integer rounds like prolog') :-
    A = array{}.fromlist([2.5, -2.5, 0.5, -0.4], [device(c)]),
    C = A.as(integer),
    C.tolist() == [3, -3, 1, 0],
    C.dtype() == int8.

test('sqrt of float and integer arrays') :-
    A = array{}.fromlist([1.0, 4.0], [device(c)]),
    B = array{}.fromlist([1, 4], [device(c)]),
    C @= sqrt(A),
    D @= sqrt(B),
    C.tolist() == [1.0, 2.0],
    D.tolist() == [1.0, 2.0].

test('derived comparisons are boolean') :-
    A = array{}.fromlist([1, 2, 3], [device(c)]),
    C @= (A =:= 2),
    D @= (A =\= 2),
    C.tolist() == [0, 1, 0],
    D.tolist() == [1, 0, 1],
    C.dtype() == bool,
    D.dtype() == bool.

test('as boolean with mixed signs') :-
    A = array{}.fromlist([-2, 0, 2], [device(c)]),
    C = A.as(boolean),
    C.tolist() == [1, 0, 1].

test('uint32 product widened to uint64') :-
    A = array{}.fromlist([0, 70000], [device(c)]),
    C @= A * A,
    C.tolist() == [0, 4900000000],
    C.dtype() == uint64.

test('negation of large uint32') :-
    A = array{}.fromlist([0, 3000000000], [device(c)]),
    C @= -A,
    C.tolist() == [0, -3000000000].

test('int32 sum widened to int64') :-
    A = array{}.fromlist([-2000000000, 2000000000], [device(c)]),
    C @= A + A,
    C.tolist() == [-4000000000, 4000000000].

test('compare uint32 with negative int8') :-
    A = array{}.fromlist([0, 70000], [device(c)]),
    B = array{}.fromlist([-5, -1], [device(c)]),
    C @= (A < B),
    D @= (B < A),
    C.tolist() == [0, 0],
    D.tolist() == [1, 1].

test('large integer plus float') :-
    A = array{}.fromlist([16777217, 1], [device(c)]),
    C @= A + 0.5,
    C.tolist() == [16777217.5, 1.5].

test('unbounded empty arrays') :-
    A = array{}.empty([2], [device(c)]),
    B = array{}.empty([2], [device(c), dtype(integer)]),
    A.tolist() == [0.0, 0.0],
    B.tolist() == [0, 0],
    B.dtype() == int64.

test('log reaching zero') :-
    A = array{}.fromlist([0.0, 1.0], [device(c)]),
    C @= log(A),
    C.tolist() == [-1.0Inf, 0.0].

test('floats default to float64') :-
    A = array{}.fromlist([1.5, 2.5], [device(c)]),
    C @= A * A,
    C.tolist() == [2.25, 6.25],
    A.dtype() == float64,
    C.dtype() == float64.

test('realized format survives a narrowed range') :-
    A = array{}.fromlist([0, 100], [device(c)]),
    B = array{}.fromlist([200, 0], [device(c)]),
    X @= A + B,
    X1 = X.realize(),
    X1.dtype() == uint16,
    array{range: R} :< X1,
    R::real(0, 200),
    X1.dtype() == uint16,
    X1.tolist() == [200, 100].

test('max keeps the dtype of its input') :-
    A = array{}.fromlist([[1, 5], [4, 2]], [device(c)]),
    C = A.max([1]),
    C.tolist() == [5, 4],
    C.dtype() == uint8.

% a mask bounded on both sides is a conjunction of conditions
test('padding on both sides') :-
    A = array{}.fromlist([1, 2], [device(c)]),
    C @= A.pad([1-1]) + 1,
    C.tolist() == [1, 2, 3, 1].

test('padding in two dimensions then sum') :-
    A = array{}.fromlist([[1, 2], [3, 4]], [device(c)]),
    B @= A.pad([1-0, 0-2]) + 1,
    B.tolist() == [[1, 1, 1, 1], [2, 3, 1, 1], [4, 5, 1, 1]],
    C = A.pad([1-1, 1-1]).sum(),
    C.tolist() == 10.

:- end_tests(c_dtype).
