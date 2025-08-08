:- module(array, [
   op(600, fy, :),
   op(600, fy, ::),
   op(600, xfy, ::),
	op(100, yf,  [])    % support block notation
]).

% :- use_module(library(arithmetic_types), []).
:- use_module(library(clpfd), except([sum/3])).
:- use_module(library(dcg/basics)).
:- use_module(library(dcg/high_order)).

% :- arithmetic_function([]/2).

product(L, Rel, Product) :-
   foldl([A, B, A*B]>>(true), L, 1, Expr),
   call(Rel, Expr, Product).

shape_size(Shape, Size) :-
   % msort is used to improve product constraint propagation.
   % by putting vars first and grounded term last.
   msort(Shape, SortedShape),
   product(SortedShape, #=, Size).

compatible_shape_strides([], [], [], []).
compatible_shape_strides([Dim | Shape], Strides, [NewDim | NewShape], NewStrides) :-
   zcompare(Order, Dim, NewDim),
   compatible_shape_strides(
      Order,
      [Dim | Shape], Strides,
      [NewDim | NewShape], NewStrides).

compatible_shape_strides(=, Shape, Strides, NewShape, NewStrides) :-
   shape_strides_equal(Shape, Strides, NewShape, NewStrides).
compatible_shape_strides(<, Shape, Strides, NewShape, NewStrides) :-
   shape_strides_less(Shape, Strides, NewShape, NewStrides).
compatible_shape_strides(>, Shape, Strides, NewShape, NewStrides) :-
   shape_strides_greater(Shape, Strides, NewShape, NewStrides).

shape_strides_equal([Dim | Shape], [Stride | Strides],
                    [NewDim | NewShape], [NewStride | NewStrides]) :-
   Dim #= NewDim,
   Stride #= NewStride,
   shape_strides_skip_one(Shape, Strides, NewShape, NewStrides).
shape_strides_less(
      [Dim | Shape], [Stride | Strides], [NewDim | NewShape], NewStrides) :-
   Dim #< NewDim,
   shape_strides_merge(Shape, Strides, [NewDim | NewShape], NewStrides, Dim, Stride).
shape_strides_greater(
      [Dim | Shape], Strides, [NewDim | NewShape], [NewStride | NewStrides]) :-
   Dim #> NewDim,
   shape_strides_merge(NewShape, NewStrides, [Dim | Shape], Strides, NewDim, NewStride).

shape_strides_merge(
      [Dim | Shape], [Stride | Strides], NewShape, NewStrides, PrevDim, PrevStride) :-
   CurDim #= PrevDim * Dim,
   PrevStride #= Dim * Stride,
   compatible_shape_strides([CurDim | Shape], [Stride | Strides], NewShape, NewStrides).

shape_strides_skip_one(Shape, Strides, NewShape, NewStrides) :-
   skip_one(Shape, Strides, Shape1, Strides1),
   skip_one(NewShape, NewStrides, NewShape1, NewStrides1),
   compatible_shape_strides(Shape1, Strides1, NewShape1, NewStrides1).

skip_one([], [], [], []).
skip_one([Dim | Shape], Strides, Shape1, Strides1) :-
   zcompare(Order, Dim, 1),
   skip_one(Order, [Dim | Shape], Strides, Shape1, Strides1).
skip_one(=, [1 | Shape], [Stride | Strides], Shape1, Strides1) :-
   (  Stride #= 0
   -> true
   ;  true
   ),
   skip_one(Shape, Strides, Shape1, Strides1).
skip_one(>, Shape, Strides, Shape, Strides).

contiguous([], [], 1).
contiguous([_ | Shape], [Stride | Strides], Contiguous) :-
   last([Stride | Strides], LastStride),
   foldl(contiguous_, Shape, Strides, Stride-(LastStride #= 1), _-Expr),
   Expr #<==> Contiguous.

contiguous_(Dim, Stride, PrevStride-Expr, Stride-NewExpr) :-
   NewExpr = (Expr #/\ (PrevStride #= Dim * Stride)).

shape_type_list(Device, Shape, DType, X), dtype(Device, X, Type) =>
   Shape = [],
   DType = Type.
shape_type_list(Device, Shape, DType, L), is_list(L) =>
   length(L, Dim),
   Shape = [Dim | Dims],
   maplist(shape_type_list(Device, Dims, DType), L).

dtype(is, true, Type) => Type = boolean.
dtype(is, false, Type) => Type = boolean.
dtype(is, X, Type), integer(X) => Type = integer.
dtype(is, X, Type), float(X) => Type = float.
dtype(is, X, _Type), var(X) => true.
dtype(is, _, _) => fail.

shape_list([], _).
shape_list([Dim | Shape], L) :-
   length(L, Dim),
   maplist(shape_list(Shape), L).

mutable(Data, Options) :-
   compound_name_arity(Data, data, Size),
   (  option(mutable(false), Options, false)
   -> arg(Size, Data, false)
   ;  true
   ).

foldlarray(Goal, Iter, Start, End) :-
   reset(Iter, V, Next),
   (  Next == 0
   -> true
   ;  call(Goal, V, Start, Tmp),
      foldlarray(Goal, Next, Tmp, End)
   ).
maparray(Goal, Iter) :-
   reset(Iter, V, Next),
   (  Next == 0
   -> true
   ;  call(Goal, V),
      maparray(Goal, Next)
   ).
maparray(Goal, Iter1, Iter2) :-
   reset(Iter1, V1, Next1),
   reset(Iter2, V2, Next2),
   (  Next1 == 0, Next2 == 0
   -> true
   ;  call(Goal, V1, V2),
      maparray(Goal, Next1, Next2)
   ).
maparray(Goal, Iter1, Iter2, Iter3) :-
   reset(Iter1, V1, Next1),
   reset(Iter2, V2, Next2),
   reset(Iter3, V3, Next3),
   (  Next1 == 0, Next2 == 0, Next3 == 0
   -> true
   ;  call(Goal, V1, V2, V3),
      maparray(Goal, Next1, Next2, Next3)
   ).

iterate_index(Shape) :-
   iterate_index(Shape, 0, []).
iterate_index([], _, RIndex) :-
   reverse(RIndex, Index),
   shift(Index).
iterate_index([Dim | Shape], C, R) :-
   (  Dim == C
   -> true
   ;  iterate_index(Shape, 0, [C | R]),
      C1 is C + 1,
      iterate_index([Dim | Shape], C1, R)
   ).

iterate_offset(Array) :-
   iterate_offset(Array.shape, Array.strides, 0).
iterate_offset([], [], Offset) :-
   shift(Offset).
iterate_offset([Dim | Shape], [Stride | Strides], C) :-
   (  Dim #= 0
   -> true
   ;  iterate_offset(Shape, Strides, C),
      Dim1 #= Dim - 1,
      C1 is C + Stride,
      iterate_offset([Dim1 | Shape], [Stride | Strides], C1)
   ).
iterate_value(Array) :-
   iterate_value(iterate_offset(Array), Array).
iterate_value(Goal, Array) :-
   reset(Goal, I, Cont),
   (  Cont == 0
   -> true
   ;  shift(Array.arg_(I)),
      iterate_value(Cont, Array)
   ).
iterate_values(Arrays) :-
   maplist([A, iterate_value(A)]>>true, Arrays, Iters),
   iterate_values_(Iters).
iterate_values_(Iters) :-
   maplist(reset, Iters, Vs, Conts),
   (  maplist(=(0), Conts)
   -> true
   ;  shift(Vs),
      iterate_values_(Conts)
   ).

push(Lazy, Goal) :-
   (  get_attr(Lazy, array, Goals)
   -> true
   ;  Goals = []
   ),
   (  var(Lazy)
   -> put_attr(Lazy, array, [Goal | Goals])
   ;  call(Goal)
   ).

take_nth0(Index, Value, L, R) :-
   nth0(Index, L, Value, R).
put_nth0(Index, Value, R, L) :-
   nth0(Index, L, Value, R).

replace_nth0(Index, Old, New) -->
   take_nth0(Index, Old),
   put_nth0(Index, New).

swap(I1, I2) -->
   replace_nth0(I1, V1, V2),
   replace_nth0(I2, V2, V1).

advanced_index_iterate_value(M, Pre, Iter, Post) :-
   reset(Iter, Is, Cont),
   (  Cont == 0
   -> true
   ;  append([Pre, Is, Post], Index),
      M1 = M.simple_index(Index),
      iterate_value(M1),
      advanced_index_iterate_value(M, Pre, Cont, Post)
   ).

positive_index(Index, Dim, PositiveIndex) :-
   (  Index == sup
   -> I = Dim
   ;  I = Index
   ),
   I #>= Dim #<==> OverTheEnd,
   PositiveIndex #= max(min(I, Dim-1), -Dim) mod Dim + OverTheEnd.

start_end_stop(Start:End:Step, Start1, End1, Step1) =>
   Start = Start1,
   End = End1,
   Step = Step1.
start_end_stop(:, Start1, End1, Step1) =>
   0 = Start1,
   sup = End1,
   1 = Step1.
start_end_stop(:End:Step, Start1, End1, Step1) =>
   0 = Start1,
   End = End1,
   Step = Step1.
start_end_stop(:End, Start1, End1, Step1) =>
   0 = Start1,
   End = End1,
   1 = Step1.
start_end_stop(Start:End, Start1, End1, Step1) =>
   Start = Start1,
   End = End1,
   1 = Step1.
start_end_stop(::Step, Start1, End1, Step1) =>
   0 = Start1,
   sup = End1,
   Step = Step1.
start_end_stop(Start::Step, Start1, End1, Step1) =>
   Start = Start1,
   sup = End1,
   Step = Step1.
start_end_stop(_, _, _, _) =>
   fail.

list_step([H | T], Step) :-
   foldl({Step}/[A, B, A]>>(Step #= A - B), T, H, _).

index_shape_strides_offset([], _Shape, Strides, NewStrides, Offset) =>
   NewStrides = Strides,
   Offset = 0.
index_shape_strides_offset(
      [I | Index], [Dim | Shape], [Stride | Strides], NewStrides, Offset
      ), start_end_stop(I, Start, _End, Step) =>
   NewStride #= Stride * Step,
   NewStrides = [NewStride | NewStridesRest],
   Step #< 0 #<==> Reverse,
   Offset #= Reverse * Dim * Stride + Start * Stride + SubOffset,
   index_shape_strides_offset(Index, Shape, Strides, NewStridesRest, SubOffset).
index_shape_strides_offset(
      [I | Index], [_Dim | Shape], [Stride | Strides], NewStrides, Offset),
      (var(I) ; integer(I)) =>
   Offset #= I * Stride + SubOffset,
   index_shape_strides_offset(Index, Shape, Strides, NewStrides, SubOffset).
index_shape_strides_offset(_, _, _, _, _) =>
   fail.

index_shape([], NewIndex, Shape, NewShape) =>
   NewShape = Shape,
   NewIndex = [].
index_shape([I | Index], NewIndex, [Dim | Shape], NewShape),
      start_end_stop(I, Start, End, Step) =>
   positive_index(Start, Dim, PositiveStart),
   positive_index(End, Dim, PositiveEnd),
   Size #= max(0, abs(PositiveEnd - PositiveStart)),
   NewDim #= Size div abs(Step) + min(1, Size mod abs(Step)),
   NewShape = [NewDim | NewShapeRest],
   NewIndex = [PositiveStart:PositiveEnd:Step | NewIndexRest],
   index_shape(Index, NewIndexRest, Shape, NewShapeRest).
index_shape([I | Index], NewIndex, [Dim | Shape], NewShape), is_list(I) =>
   Array = array{lazy:false}.from_list(I),
   index_shape([Array | Index], NewIndex, [Dim | Shape], NewShape).
index_shape([I | Index], NewIndex, [_Dim | Shape], NewShape),
      is_dict(I, array), I.dtype = integer =>
   NewIndex = [I | NewIndexRest],
   append(I.shape, NewShapeRest, NewShape),
   index_shape(Index, NewIndexRest, Shape, NewShapeRest).
index_shape([I | Index], NewIndex, [Dim | Shape], NewShape) =>
   dim_index(Dim, I),
   positive_index(I, Dim, NewI),
   NewIndex = [NewI | NewIndexRest],
   index_shape(Index, NewIndexRest, Shape, NewShape).

dim_index(Dim, I) :-
   I #>= -Dim,
   I #< Dim.

promote(X, Y), is_dict(X, array) =>
   X = Y.
promote(X, Y), number(X) =>
   Y = array{}.full([], X).

broadcast(Arrays, NewArrays) :-
   maplist(promote, Arrays, Arrays1),
   maplist(get_dict(shape), Arrays1, Shapes),
   maplist(get_dict(strides), Arrays1, Strides),
   broadcast(Shapes, Strides, NewShape, NewStrides),
   maplist(
      {NewShape}/[Stride, Array, NewArray]>>(
         put_dict([shape=NewShape, strides=Stride], Array, NewArray)),
      NewStrides, Arrays1, NewArrays).

broadcast(Shapes, Strides, NewShape, NewStrides) :-
   maplist(length, Shapes, Lengths),
   max_list(Lengths, L),
   maplist(pad(1, L), Shapes, PaddedShapes),
   maplist(pad(0, L), Strides, PaddedStrides),
   maplist(reverse, PaddedShapes, RPaddedShapes),
   maplist(reverse, PaddedStrides, RPaddedStrides),
   same_length(RPaddedShapes, RPairs),
   maplist(pairs_keys_values, RPairs, RPaddedShapes, RPaddedStrides),
   transpose(RPairs, RPairsT),
   maplist(broadcast_pairs, RPairsT, RNewShape, RNewStridesT),
   transpose(RNewStridesT, RNewStrides),
   maplist(reverse, RNewStrides, NewStrides),
   reverse(RNewShape, NewShape).

pad(V, Length, ShapeIn, ShapeOut) :-
   length(ShapeOut, Length),
   length(ShapeIn, InLength),
   PadLength is Length - InLength,
   length(Padding, PadLength),
   append(Padding, ShapeIn, ShapeOut),
   maplist(=(V), Padding).
  
broadcast_pairs(Pairs, D, Strides) :-
   foldl(broadcast_shape, Pairs, 1, D),
   maplist(broadcast_stride(D), Pairs, Strides).

broadcast_shape(D2-_, D1, D) :-
   D1 #\= 1 #/\ D1 #= D
   #\ D1 #= 1 #/\ D2 #= D,
   D2 #\= 1 #/\ D2 #= D
   #\ D2 #= 1 #/\ D1 #= D.
broadcast_stride(D, D1-S1, S2) :-
   D #= D1 #/\ S1 #= S2
   #\ D #\= D1 #/\ S2 #= 0.

M.contiguous() := Contiguous :-
   Contiguous = contiguous(M.shape, M.strides, Contiguous).
M.size() := Size :-
   shape_size(M.shape, Size).
M.to(Device) := Dict :-
   Dict = M.put([device: Device]).
M.arg_offset(Offset) := I :-
   I #= (Offset + M.offset) mod M.buffersize + 1.
M.arg_(Offset) := V :-
   arg(M.arg_offset(Offset), M.data(), V).
M.setarg_(Offset, Value) := M :-
   setarg(M.arg_offset(Offset), M.data(), Value).
M.index_offset(Index) := Offset :-
   maplist([A, B, C]>>(C #= A*B), Index, M.strides, Prod),
   clpfd:sum(Prod, #=, Offset).
M.readonly() := M :-
   push(M.lazy, mutable(M.data, [mutable(false)])).

M.data() := M.data :-
   Lazy = M.lazy,
   (  var(Lazy), get_attr(Lazy, array, Goals)
   -> del_attr(Lazy, array),
      reverse(Goals, RGoals),
      maplist(call, RGoals)
   ;  true
   ).

M.default() := Dict :-
   Dict = M.default([]).
M.default(Options) := Dict :-
   dict_options(M, MOptions),
   merge_options(Options, MOptions, Merged),
   option(dtype(DType), Merged, float),
   option(device(Device), Merged, is),
   option(offset(Offset), Merged, 0),
   option(lazy(Lazy), Merged, _),
   Dict = array{dtype:DType, device:Device, offset:Offset, lazy: Lazy}.

M.empty(Shape) := Dict :-
   Dict = M.empty(Shape, []).
M.empty(Shape, Options) := Dict :-
   same_length(Shape, Strides),
   shape_size(Shape, Size),
   contiguous(Shape, Strides, 1),
   Size1 is Size + 1,
   Dict = M.default().put([
      data: Data, shape: Shape, strides: Strides, buffersize: Size]),
   push(Dict.lazy, (
      compound_name_arity(Data, data, Size1),
      mutable(Data, Options)
   )).

M.from_list(List) := Dict :-
   Dict = M.from_list(List, []).
M.from_list(List, Options) := Dict :-
   DType = M.get(dtype, _),
   M1 = M.default(),
   shape_type_list(M1.device, Shape, DType, List),
   same_length(Shape, Strides),
   shape_size(Shape, Size),
   contiguous(Shape, Strides, 1),
   Dict = M1.put([
      data: Data, shape: Shape, strides: Strides, dtype: DType, buffersize: Size]),
   push(Dict.lazy, (
      flatten(List, ListData),
      append(ListData, [_], ListData1),
      compound_name_arguments(Data, data, ListData1),
      mutable(Data, Options)
   )).

M.ones(Shape) := Dict :-
   Dict = M.ones(Shape, []).
M.ones(Shape, Options) := Dict :-
   Dict = M.full(Shape, 1, Options).
M.zeros(Shape) := Dict :-
   Dict = M.zeros(Shape, []).
M.zeros(Shape, Options) := Dict :-
   Dict = M.full(Shape, 0, Options).

M.full(Shape, FillValue) := Dict :-
   Dict = M.full(Shape, FillValue, []).
M.full(Shape, FillValue, Options) := Dict :-
   same_length(Shape, Strides),
   maplist(=(0), Strides),
   Dict = M.empty([1], Options).put([shape=Shape, strides=Strides]),
   push(Dict.lazy, maparray([FillValue]>>true, Dict.iter())).


M.arange(Stop) := Dict :-
   Dict = M.arange(Stop, []).
M.arange(Stop, Options) := Dict :-
   Dict = M.arange(0, Stop, Options).
M.arange(Start, Stop, Options) := Dict :-
   Dict = M.arange(Start, Stop, 1, Options).
M.arange(Start, Stop, Step, Options) := Dict :-
   Size is ceil(abs((Stop - Start) / Step)),
   Dict = M.empty([Size], Options),
   push(Dict.lazy, 
        foldlarray({Step}/[Prev, Prev, Next]>>(Next is Prev + Step),
                   Dict.iter(), Start, _)).

M.eye(N) := Dict :-
   Dict = M.full([N], 0).copy([mutable(true)]).put([shape=[N, N], strides=[-1, 1]]),
   push(Dict.lazy, eye_kernel(Dict)).
eye_kernel(Array) :-
   Array = Array.setarg_(0, 1).readonly().

M.to_list() := R :-
   shape_list(M.shape, R),
   flatten(R, List),
   foldl([V, Iter, Next]>>reset(Iter, V, Next), List, M.iter(), _).

M.iter() := Cont :-
   Cont = M.iter_value().
M.iter_value() := Cont :-
   Cont = iterate_value(M).
M.iter_offset() := Cont :-
   Cont = iterate_offset(M).
M.iter_index() := Cont :-
   Cont = iterate_index(M.shape).

M.copy() := R :-
   R = M.copy([]).
M.copy(Options) := R :-
   R = M.empty(M.shape, Options),
   push(R.lazy, maparray(=, M.iter(), R.iter())).

M.reshape(Shape) := Dict :-
   Shape ins 0..sup,
   shape_size(Shape, M.size()),
   (  compatible_shape_strides(M.shape, M.strides, Shape, Strides)
   -> Dict = M.put([shape=Shape, strides=Strides])
   ;  Dict = M.copy().reshape(Shape)
   ).


M.t() := Dict :-
   reverse(M.shape, Shape),
   reverse(M.strides, Strides),
   Dict = M.put([shape=Shape, strides=Strides]).

M.swapaxes(Axis1, Axis2) := Dict :-
   swap(Axis1, Axis2, M.shape, Shape),
   swap(Axis1, Axis2, M.strides, Strides),
   Dict = M.put([shape=Shape, strides=Strides]).

M.ndim() := NDim :-
   length(M.shape, NDim).

split_index(A, S, R), (is_dict(A, array) ; integer(A)) => A = R, S = ':' .
split_index(A, R, S) => A = R, S = ':' .

M.index(Index) := Dict :-
   index_shape(Index, NewIndex, M.shape, _),
   (  member(I, NewIndex), is_dict(I, array)
   -> maplist(split_index, NewIndex, SimpleIndex, AdvancedIndex),
      M1 = M.simple_index(SimpleIndex),
      Dict = M1.advanced_index(AdvancedIndex)
   ;  Dict = M.simple_index(Index)
   ).
M.simple_index(Index) := Dict :-
   index_shape(Index, NewIndex, M.shape, Shape),
   index_shape_strides_offset(NewIndex, M.shape, M.strides, Strides, NewOffset),
   Offset #= M.offset + (NewOffset mod M.buffersize),
   Dict = M.put([shape=Shape, strides=Strides, offset=Offset]).
M.advanced_index(Index) := Dict :-
   % missing interleaving of simple and advanced indexing
   % missing boolean indexing
   include([A]>>once(is_dict(A, array) ; integer(A)), Index, Arrays),
   broadcast(Arrays, BArrays),
   once(append([PreSlice, Arrays, PostSlice], Index)),
   same_length(PreSlice, PreShape),
   same_length(Arrays, ArraysShape),
   once(append([PreShape, ArraysShape, PostShape], M.shape)),
   BArrays = [Array | _],
   append([PreShape, Array.shape, PostShape], Shape),
   Dict = M.empty(Shape),
   push(Dict.lazy, maparray(=, Dict.iter(),
      advanced_index_iterate_value(M, PreSlice, iterate_values(BArrays), PostSlice))).

squeeze_(Axis) -->
   take_nth0(Axis, Dim-_),
   (  {Dim = 1}
   -> []
   ;  {domain_error(1, Dim)}
   ).

M.squeeze(Axis) := Dict :-
   sort(0, @>=, Axis, SortedAxis),
   pairs_keys_values(Pairs, M.shape, M.strides),
   phrase(sequence(squeeze_, SortedAxis), Pairs, NewPairs),
   pairs_keys_values(NewPairs, NewShape, NewStrides),
   Dict = M.put([shape=NewShape, strides=NewStrides]).

M.broadcast(Other) := Dict :-
   broadcast([M, Other], [Dict, Other]).

M.max() := Dict :-
   Dict = M.max([]).
M.max(Options) := Dict :-
   (  option(axis(Axis), Options)
   -> phrase(replace_nth0(Axis, _, 1), M.shape, Shape),
      M1 = M.zeros(Shape).copy([mutable(true)])
   ;  M1 = M.zeros([1], [mutable(true)]),
      Axis = 0
   ),
   M2 = M1.broadcast(M),
   push(M2.lazy, maparray(max_kernel(M2), M.iter(), M2.iter_offset())),
   (  option(keepdims(false), Options, false)
   -> Dict = M1.squeeze([Axis])
   ;  Dict = M1
   ).

M.argmax() := Dict :-
   Dict = M.argmax([]).
M.argmax(Options) := Dict :-
   (  option(axis(Axis), Options)
   -> phrase(replace_nth0(Axis, _, 1), M.shape, Shape),
      MaxArray = M.zeros(Shape).copy([mutable(true)]),
      IndexArray = M.put([dtype:integer]).empty(Shape, [mutable(true)]),
      M1 = M
   ;  MaxArray = M.zeros([1], [mutable(true)]),
      IndexArray = M.put([dtype:integer]).empty([1], [mutable(true)]),
      M1 = M.reshape([_]),
      Axis = 0
   ),
   MaxArray1 = MaxArray.broadcast(M),
   IndexArray1 = IndexArray.broadcast(M),
   push(IndexArray1.lazy, maparray(argmax_kernel(Axis, MaxArray1, IndexArray1), M1.iter_index(), M1.iter(), MaxArray1.iter_offset())),
   (  option(keepdims(false), Options, false)
   -> Dict = IndexArray.squeeze([Axis])
   ;  Dict = IndexArray
   ).

max_kernel(MaxArray, Value, MaxOffset) :-
   Max = MaxArray.arg_(MaxOffset),
   (  Value > Max
   -> _ = MaxArray.setarg_(MaxOffset, Value)
   ;  true
   ).
argmax_kernel(Axis, MaxArray, IndexArray, Index, Value, MaxOffset) :-
   Max = MaxArray.arg_(MaxOffset),
   (  Value > Max
   -> _ = MaxArray.setarg_(MaxOffset, Value),
      nth0(Axis, Index, I),
      _ = IndexArray.setarg_(MaxOffset, I)
   ;  true
   ).


:- begin_tests(array).

test('single element indexing') :-
   X = array{}.arange(10),
   2 = X.index([2]).to_list(),
   8 = X.index([-2]).to_list(),
   Y = X.reshape([2, 5]),
   8 = Y.index([1, 3]).to_list(), 
   9 = Y.index([1, -1]).to_list(),
   [0, 1, 2, 3, 4] = Y.index([0]).to_list(),
   2 = Y.index([0]).index([2]).to_list().

test('slicing and striding') :-
   X = array{lazy:false}.from_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
   [1, 3, 5] = X.index([1:7:2]).to_list(),
   [8, 9] = X.index([-2:10]).to_list(),
   [7, 6, 5, 4] = X.index([-3:3: -1]).to_list(),
   [5, 6, 7, 8, 9] = X.index([5:sup]).to_list().
test('slicing and striding 2') :-
   X = array{}.from_list([[[1],[2],[3]], [[4],[5],[6]]]),
   [[[4], [5], [6]]] = X.index([1:2]).to_list().

test('advanced indexing') :-
   X = array{}.arange(10, 1, -1, []),
   [7, 7, 9, 2] = X.index([[3, 3, 1, 8]]).to_list(),
   [7, 7, 4, 2] = X.index([[3, 3, -3, 8]]).to_list(),
   Y = array{}.from_list([[1, 2], [3, 4], [5, 6]]),
   [[3, 4], [5, 6]] = Y.index([[1, -1]]).to_list(),
   \+ _ = Y.index([[3, 4]]).to_list().

test('advanced indexing 2') :-
   X = array{}.arange(35).reshape([5, 7]),
   [0, 15, 30] = X.index([[0, 2, 4], [0, 1, 2]]).to_list(),
   \+ _ = X.index([[0, 2, 4], [0, 1]]).to_list(),
   [1, 15, 29] = X.index([[0, 2, 4], 1]).to_list(),
   [[ 0,  1,  2,  3,  4,  5,  6],
    [14, 15, 16, 17, 18, 19, 20],
    [28, 29, 30, 31, 32, 33, 34]] = X.index([[0, 2, 4]]).to_list().

test('advanced indexing 3') :-
   X = array{}.from_list([[1,2],[3, 4],[5,6]]),
   [1, 4, 5] = X.index([[0, 1, 2], [0, 1, 0]]).to_list().

test('advanced indexing corners') :-
   X = array{}.from_list([[0, 1, 2], [3, 4, 5], [6, 7, 8], [9, 10, 11]]),
   Rows = array{}.from_list([[0, 0], [3, 3]]),
   Columns = array{}.from_list([[0, 2], [0, 2]]),
   [[0, 2], [9, 11]] = X.index([Rows, Columns]).to_list().
test('advanced indexing corners 2') :-
   X = array{}.from_list([[0, 1, 2], [3, 4, 5], [6, 7, 8], [9, 10, 11]]),
   Rows = array{}.from_list([0, 3]),
   Columns = array{}.from_list([0, 2]),
   [[0, 2], [9, 11]] = X.index([Rows.reshape([2, 1]), Columns]).to_list(),
   [0, 11] = X.index([Rows, Columns]).to_list().

:- end_tests(array).
% '@='(Left, Right) :-
%    array_eval(Right, Left).
%
% binary_op(_+_) => true.
% binary_op(_-_) => true.
% binary_op(_*_) => true.
% binary_op(_/_) => true.
% binary_op(_) => fail.
%
% array_eval(BinaryOp, C), binary_op(BinaryOp) =>
%    compound_name_arguments(BinaryOp, Op, [A, B]),
%    array_eval(A, A1),
%    array_eval(B, B1),
%    broadcast([A1, B1], [A2, B2]),
%    dicts_slice([dtype, device], [A2, B2], [Out, Out]),
%    same_length(A2.shape, Strides),
%    contiguous(A2.shape, Strides, 1),
%    Expr =.. [Op, A2, B2],
%    C = Out.put([data=Expr, shape=A2.shape, strides=Strides, offset=0,
%                 size=A2.size, buffer=_, buffersize=A2.size]).
% array_eval(A @ B, C) =>
%    array_eval(A, A1),
%    array_eval(B, B1),
%    Dim1 = A.ndim(),
%    Dim2 is max(B.ndim() - 1, 1),
%    (  A.ndim() > 1, B.ndim() > 1
%    -> nth1(Dim1, Shape1, 1, A.shape),
%       nth1(Dim2, Shape2, 1, B.shape)
%    ;  Shape1 = A.shape,
%       Shape2 = B.shape
%    ),
%    A2 @= A1.reshape(Shape1),
%    B2 @= B1.reshape(Shape2).swapaxes(B1.ndim(), Dim2),
%    A3 @= A2.swapaxes(Dim1, Dim2),
%    B3 @= B2.swapaxes(Dim1, Dim2),
%    array_eval(A3 * B3, C1),
%    Axis1 is C1.ndim() - 2,
%    C = C1.sum([Axis1]).
%
% array_eval(A, B), (is_dict(A, array) ; integer(A)) =>
%    A = B.
%
% sum_axis_shape([]) --> [].
% sum_axis_shape([Axis | OtherAxis]) -->
%    replace_nth0(Axis, _, 1),
%    sum_axis_shape(OtherAxis).
%
% M.sum(Axis) := Dict :-
%    Dict = M.sum(Axis, false).
%
% M.sum(Axis, KeepDim) := Dict :-
%    phrase(sum_axis_shape(Axis), M.shape, Shape),
%    Res = M.empty(Shape, [zero(true)]),
%    array_eval(M+Res, Res2),
%    Res2.data = _ + BroadcastedRes,
%    Res3 = BroadcastedRes.put([data=Res2.data]),
%    Res4 = Res3.put([data=view(Res3), shape=Shape, size=Res.size]),
%    (  KeepDim
%    -> Dict = Res4
%    ;  Dict = Res4.squeeze(Axis)
%    ).
%
%
% realize(Outputs) :-
%    compile(c, Outputs).
%
% M.to_list() := L :-
%    to_list_(M, L).
%
% to_list_(M, L) :-
%    realize([M]),
%    M.buffer.data = pointer(Buffer, Offset),
%    to_list(L, Buffer, M.dtype, Offset, M.buffersize).
%
% test_matmul(C) :-
%    Size = 1024,
%    A @= array{name:a, dtype: float64}.empty([Size, Size], [zero(true)]),
%    B @= array{name:b, dtype: float64}.empty([Size, Size], [zero(true)]),
%    C @= A @ B, realize([C]).
%
% :- begin_tests(array).
%
% test(reshape_1) :-
%    _ = array{}.arange(12).reshape([12, 1, 1]).
%
% test(broadcast_shape_1) :-
%    broadcast_shape(1-_, 1, D),
%    D == 1.
% test(broadcast_shape_2) :-
%    broadcast_shape(1-_, 3, D),
%    D == 3.
% test(broadcast_shape_3) :-
%    broadcast_shape(3-_, 1, D),
%    D == 3.
% test(broadcast_shape_4) :-
%    broadcast_shape(3-_, 3, D),
%    D == 3.
% test(broadcast_shape_4) :-
%    broadcast_shape(X-_, 1, D),
%    D == X.
% test(broadcast_shape_5) :-
%    broadcast_shape(_X-_, 3, D),
%    D == 3.
% test(broadcast_shape_6) :-
%    broadcast_shape(1-_, X, D),
%    D == X.
% test(broadcast_shape_7) :-
%    broadcast_shape(3-_, _X, D),
%    D == 3.
%
% test('reshape_3_4') :-
%    A = array{}.arange(12),
%    B = A.reshape([3, 4]),
%    B.strides == [4, 1].
%
% test('index_integer') :-
%    A = array{}.arange(12),
%    B = A.index([5]),
%    B.offset == 5,
%    B.shape == [],
%    B.strides == [].
%
% test('index_slice_identity') :-
%    A = array{}.arange(12),
%    B = A.index([:]),
%    B.shape == [12],
%    B.strides == [1],
%    B.offset == 0.
%
% test('index_slice_start') :-
%    A = array{}.arange(12),
%    B = A.index([6:sup]),
%    B.shape == [6],
%    B.offset == 6.
%
% test('index_slice_end') :-
%    A = array{}.arange(12),
%    B = A.index([:6]),
%    B.shape == [6].
%
% test('index_slice') :-
%    A = array{}.arange(12),
%    B = A.index([6:sup]),
%    B.shape == [6],
%    B.offset == 6.
%
% test('index_slice_neg') :-
%    A = array{}.arange(12),
%    B = A.index([2: -2]),
%    B.shape == [8],
%    B.offset == 2.
%
% test('index_slice_iter') :-
%    A = array{}.arange(12),
%    B = A.index([::(3)]),
%    B.shape == [4],
%    B.strides == [3].
%
% test('index_slice_reverse_iter') :-
%    A = array{}.arange(12),
%    B = A.index([::(-3)]),
%    B.shape == [4],
%    B.strides == [-3],
%    B.offset == 11.
%
% test('index_slice_full') :-
%    A = array{}.arange(12),
%    B = A.index([2: -2:3]),
%    B.shape == [3],
%    B.strides == [3],
%    B.offset == 2.
%
% test('index_2d') :-
%    A = array{}.arange(12).reshape([3, 4]),
%    B = A.index([1, 1]),
%    B.shape == [],
%    B.strides == [],
%    B.offset == 5.
%
% test('index_2d_slice') :-
%    A = array{}.arange(12).reshape([3, 4]),
%    B = A.index([1:3, 1:3]),
%    B.shape == [2, 2],
%    B.strides == [4, 1],
%    B.offset == 5.
%
% test('index_3d_slice') :-
%    A = array{}.arange(12).reshape([3, 2, 2]),
%    B = A.index([1:3, 1:2, 1:2]),
%    B.shape == [2, 1, 1],
%    B.strides == [4, 2, 1],
%    B.offset == 7.
%
% test('index_3d_slice2') :-
%    A = array{}.arange(12).reshape([3, 2, 2]),
%    B = A.index([:, :: -1]),
%    B.shape == [3, 2, 2],
%    B.strides == [4, -2, 1],
%    B.offset == 2.
%
% test('index_list') :-
%    A = array{}.arange(12),
%    B = A.index([[1, 2, 3]]),
%    B.shape == [3],
%    B.strides == [1],
%    B.offset == 1.
%
% test('index_list_copy') :-
%    A = array{}.arange(12),
%    B = A.index([[1, 2, 4]]),
%    B.shape == [3],
%    B.strides == [1],
%    B.offset == 0.
%
% % test('iterate_1') :-
% %    A = array{}.arange(12).iterate(),
% %    A == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11].
% %
% % test('iterate_2') :-
% %    A = array{}.arange(12).reshape([3, 2, 2]).index([:, :: -1]).iterate(),
% %    A = [[[2, 3], [0, 1]], [[6, 7], [4, 5]] | _].
%
% test('copy_reshape') :-
%    X = array{}.arange(12).reshape([3, 4]).index([1:3, 1:3]).reshape([4]),
%    X.shape == [4],
%    X.strides == [1],
%    X.offset = 0.
%
% test(add_broadcast) :-
%    C @= array{}.arange(12) + 1,
%    C.shape == [12].
%
% test(add_broadcast_2) :-
%    C @= array{}.arange(4).reshape([4, 1]) * array{}.arange(3),
%    C.shape == [4, 3].
%
% test(sum) :-
%    C @= array{}.arange(12).reshape([3, 2, 2]).sum([0, 2], false),
%    [27, 39] == C.to_list().
%
% test(matmul) :-
%    A @= array{name:a}.arange(16).reshape([4, 4]),
%    B @= array{name:b}.arange(16).reshape([4, 4]),
%    C @= A @ B,
%    [56,62,68,74,152,174,196,218,248,286,324,362,344,398,452,506] == C.to_list().
%
% :- end_tests(array).
