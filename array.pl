:- module(array, []).

:- use_module(library(clpfd)).
:- use_module(library(pairs)).

view:_.from_shape(Shape) := View :-
   shape_strides(Shape, Strides),
   shape_mask(Shape, Mask),
   View = view{shape: Shape, strides: Strides, mask: Mask, offset: 0}.

view:M.reshape(Shape) := Dict :- % FIXME: This needs to handle masks and offsets
   merge_dims(M.zip(), MergedPairs),
   Dict = M.put([shape: Shape, strides: _, mask: _]),
   merge_dims(Dict.zip(), MergedPairs).

view:M.zip() := Zip :-
   maplist([Dim, Stride, Mask, Dim-Stride-Mask]>>true, M.shape, M.strides, M.mask, Zip).

M.default() := Dict :-
   Dict = M.default([]).
M.default(Options) := Dict :-
   dict_options(M, MOptions),
   merge_options(Options, MOptions, Merged),
   option(dtype(DType), Merged, float),
   option(device(Device), Merged, prolog),
   Dict = array{views: [], dtype:DType, device:Device, data: _}.

M.push(buffer(Size)) := Dict =>
   Dict = M.push_view(view{}.from_shape([Size])).push_op(buffer(Size)).
M.push_op(Op) := Dict :-
   Dict = M.put([id: _Id, op: Op]).
M.push_view(View) := Dict :-
   Dict = M.put([views: [View | M.views]]).

M.empty(Shape) := Dict :-
   Dict = M.empty(Shape, []).
M.empty(Shape, Options) := Dict :-
   shape_size(Shape, Size),
   Dict = M.default(Options).push(buffer(Size)).reshape(Shape).

product(L, Rel, Product) :-
   foldl([A, B, A*B]>>(true), L, 1, Expr),
   call(Rel, Expr, Product).

shape_size(Shape, Size) :-
   % msort is used to improve product constraint propagation.
   % by putting vars first and grounded term last.
   msort(Shape, SortedShape),
   product(SortedShape, #=, Size).

shape_mask(Shape, Mask) :-
   same_length(Shape, Mask),
   maplist([Dim, 0-Dim1]>>(Dim1 is Dim - 1), Shape, Mask).

shape_strides([], []).
shape_strides([_ | Shape], [HeadStride | Strides]) :-
   foldl([Dim, Stride, ParentStride, Stride]>>(ParentStride #= Dim*Stride),
         Shape, Strides, HeadStride, 1).

% contiguous([_Dim | Shape], [Stride | Strides], [C | Cs]) :-
%    Stride #= CStride #<==> C,
%    contiguous(Shape, Strides, Cs, CStride).
% contiguous([], [], [], 1).
% contiguous([Dim | Shape], [Stride | Strides], [C | Cs], ParentStride) :-
%    ParentStride #= ChildStride*Dim,
%    Stride #= ChildStride #<==> C,
%    contiguous(Shape, Strides, Cs, ChildStride).

contiguous(Stride, C, [_Dim | Shape], Shape) :-
   foldl([A, B, A*B]>>true, Shape, 1, Expr),
   Expr #= Stride #<==> C.

peak(X), [X] -->
   [X].

% merge_dims(Pairs, MergedPairs) :-
%    phrase(merge_dims(Pairs, _), MergedPairs).
% merge_dims([], 1) --> [].
% merge_dims([Dim-Stride | Pairs], ParentStride) -->
%    peak(MDim-MStride),
%    {  ParentStride #= Dim*ChildStride,
%       Stride #= ChildStride #<==> C,
%       (Dim #= MDim #/\ Stride #= MStride) #<==> #\ C
%    },
%    merge_dims(C, Pairs, Dim-Stride, ChildStride).
% merge_dims(0, Pairs, Pair, CStride) -->
%    [Pair],
%    merge_dims(Pairs, CStride).
% merge_dims(1, Pairs, Pair, CStride) -->
%    merge_dims(Pairs, Pair, CStride).
% merge_dims([], Pair, 1) -->
%    [Pair].
% merge_dims([Dim-Stride | Pairs], PopDim-PopStride, ParentStride) -->
%    peak(MDim-MStride),
%    {  ParentStride #= Dim*ChildStride,
%       Stride #= ChildStride #<==> C,
%       (PopDim #= MDim #/\ PopStride #= MStride) #<==> #\ C
%    },
%    merge_dims(C, Pairs, PopDim-PopStride, Dim-Stride, ChildStride).
% merge_dims(0, Pairs, PopPair, Pair, CStride) -->
%    [PopPair, Pair],
%    merge_dims(Pairs, CStride).
% merge_dims(1, Pairs, PopDim-PopStride, Dim-Stride, CStride) -->
%    {  NewDim #= PopDim*Dim,
%       PopStride #= Dim*Stride
%    },
%    merge_dims(Pairs, NewDim-Stride, CStride).

merge_dims([], []).
merge_dims([H | T], MergedPairs) :-
   merge_dims_acc(T, H, MergedPairs).

merge_dims_acc([], Acc, [Acc]).
merge_dims_acc([Dim-Stride-(Min-Max) | T], AccDim-AccStride-AccMask, [MDim-MStrideMask | Merged]) :-
   AccStride #= Dim * Stride #<==> C,
   Max - Min + 1 #= Dim #<==> C,
   AccDim #= MDim #<==> #\ C,
   merge_dims_acc(C, [Dim-Stride | T], AccDim-AccStride-AccMask, [MDim-MStrideMask | Merged]).

merge_dims_acc(1, [Dim-Stride-_ | T], AccDim-_-_, Merged) :-
   NewAccDim #= AccDim * Dim,
   merge_dims_acc(T, NewAccDim-Stride-(0-NewAccDim), Merged).
merge_dims_acc(0, [H | T], Acc, [Acc | MergedTail]) :-
   merge_dims_acc(T, H, MergedTail).

:- begin_tests(merge_dims).

test('contiguous merge all') :-
   merge_dims([2-12-(0-1), 3-4-(0-2), 4-1-(0-3)], [24-1-(0-23)]).

:- end_tests(merge_dims).

:- begin_tests(strides).

test('strides_1') :-
   shape_strides([_], [1]).
test('strides_2') :-
   shape_strides([2, 3], [3, 1]).
test('strides_3') :-
   shape_strides([2, 3, 4], [12, 4, 1]).

:- end_tests(strides).

:- begin_tests(view).

test('from_shape') :-
   view{}.from_shape([5]) = view{shape: [5], strides: [1], mask: [0-4], offset: 0},
   view{}.from_shape([2, 3]) = view{shape: [2, 3], strides: [3, 1], mask: [0-1, 0-2], offset: 0},
   view{}.from_shape([2, 3, 4]) = view{shape: [2, 3, 4], strides: [12, 4, 1], mask: [0-1, 0-2, 0-3], offset: 0}.

:- end_tests(view).

:- begin_tests(reshape, [blocked('not implemented')]).

% ===== SUCCESSFUL RESHAPES =====
% --- Contiguous ---
test('contiguous merge') :-
  Start = view{}.from_shape([2,3,4]),
  NewShape = [6,4],
  Expected = view{}.from_shape(NewShape),
  Start.reshape(NewShape) = Expected.

test('contiguous split') :-
  Start = view{shape:[24], strides:[1], offset:0, mask:_},
  NewShape = [2,3,4],
  shape_mask(NewShape, ExpectedMask),
  Expected = view{shape:[2,3,4], strides:[12,4,1], offset:0, mask:ExpectedMask},
  Start.reshape(NewShape) = Expected.

test('contiguous to scalar') :-
  Start = view{shape:[1], strides:[1], offset:0, mask:_},
  NewShape = [],
  shape_mask(NewShape, ExpectedMask),
  Expected = view{shape:[], strides:[], offset:0, mask:ExpectedMask},
  Start.reshape(NewShape) = Expected.

test('scalar to contiguous') :-
  Start = view{shape:[], strides:[], offset:0, mask:_},
  NewShape = [1,1,1],
  shape_mask(NewShape, ExpectedMask),
  Expected = view{shape:[1,1,1], strides:[1,1,1], offset:0, mask:ExpectedMask},
  Start.reshape(NewShape) = Expected.

test('contiguous with ones') :-
  Start = view{shape:[1,10,1], strides:[10,1,1], offset:0, mask:_},
  NewShape = [10],
  shape_mask(NewShape, ExpectedMask),
  Expected = view{shape:[10], strides:[1], offset:0, mask:ExpectedMask},
  Start.reshape(NewShape) = Expected.

% --- Non-contiguous (from expand, permute) ---
test('split expanded dim') :-
  Start = view{shape:[10,10], strides:[1,0], offset:0, mask:_},
  NewShape = [10,2,5],
  shape_mask(NewShape, ExpectedMask),
  Expected = view{shape:[10,2,5], strides:[1,0,0], offset:0, mask:ExpectedMask},
  Start.reshape(NewShape) = Expected.

test('split other expanded dim') :-
  Start = view{shape:[10,10], strides:[0,1], offset:0, mask:_},
  NewShape = [10,5,2],
  shape_mask(NewShape, ExpectedMask),
  Expected = view{shape:[10,5,2], strides:[0,2,1], offset:0, mask:ExpectedMask},
  Start.reshape(NewShape) = Expected.

test('merge after permute') :-
  Start = view{shape:[3,4,2], strides:[4,1,12], offset:0, mask:_},
  NewShape = [12,2],
  shape_mask(NewShape, ExpectedMask),
  Expected = view{shape:[12,2], strides:[1,12], offset:0, mask:ExpectedMask},
  Start.reshape(NewShape) = Expected.

test('double permute with merge') :-
  Start = view{shape:[4,4,4], strides:[1,16,4], offset:0, mask:_},
  NewShape = [16,4],
  shape_mask(NewShape, ExpectedMask),
  Expected = view{shape:[16,4], strides:[4,1], offset:0, mask:ExpectedMask},
  Start.reshape(NewShape) = Expected.

% --- Masked ---
test('reshape masked view') :-
  Start = view{shape:[10], strides:[1], offset:0, mask:[2-7]},
  NewShape = [3,2],
  shape_mask(NewShape, ExpectedMask),
  Expected = view{shape:[3,2], strides:[2,1], offset:2, mask:ExpectedMask},
  Start.reshape(NewShape) = Expected.

test('reshape with offset') :-
  Start = view{shape:[6], strides:[1], offset:2, mask:_},
  NewShape = [2,3],
  shape_mask(NewShape, ExpectedMask),
  Expected = view{shape:[2,3], strides:[3,1], offset:2, mask:ExpectedMask},
  Start.reshape(NewShape) = Expected.

test('masked with pad no-op reshape') :-
  Start = view{shape:[14], strides:[1], offset: -2, mask:[2-11]},
  NewShape = [14],
  Start.reshape(NewShape) = Start.

% --- Zero shapes ---
test('zero shape to zero shape') :-
  Start = view{shape:[2,0,4], strides:[0,4,1], offset:0, mask:_},
  NewShape = [0,3,1],
  shape_mask(NewShape, ExpectedMask),
  Expected = view{shape:[0,3,1], strides:[0,0,0], offset:0, mask:ExpectedMask},
  Start.reshape(NewShape) = Expected.

test('zero shape with ones') :-
  Start = view{shape:[1,10,0], strides:[0,0,1], offset:0, mask:_},
  NewShape = [0],
  shape_mask(NewShape, ExpectedMask),
  Expected = view{shape:[0], strides:[0], offset:0, mask:ExpectedMask},
  Start.reshape(NewShape) = Expected.

% ===== FAILED RESHAPES =====
test('permute breaks contiguity', [fail]) :-
  Start = view{shape:[3,2,4], strides:[4,12,1], offset:0, mask:_},
  NewShape = [6,4],
  _ = Start.reshape(NewShape).

test('permute breaks contiguity 2', [fail]) :-
  Start = view{shape:[2,4,3], strides:[12,1,4], offset:0, mask:_},
  NewShape = [2,12],
  _ = Start.reshape(NewShape).

test('expand and permute breaks contiguity', [fail]) :-
  Start = view{shape:[2,4,3], strides:[0,1,0], offset:0, mask:_},
  NewShape = [2,12],
  _ = Start.reshape(NewShape).

test('merge expanded dim', [fail]) :-
  Start = view{shape:[10,10], strides:[1,0], offset:0, mask:_},
  NewShape = [100],
  _ = Start.reshape(NewShape).

test('non-contiguous to smaller non-contiguous', [fail]) :-
  Start = view{shape:[8,2], strides:[1,8], offset:0, mask:_},
  NewShape = [4,4],
  _ = Start.reshape(NewShape).

test('masked permute', [fail]) :-
  Start = view{shape:[2,2], strides:[1,4], offset:5, mask:_},
  NewShape = [4],
  _ = Start.reshape(NewShape).

test('masked split unaligned', [fail]) :-
  Start = view{shape:[10], strides:[1], offset:0, mask:[2-6]}, % mask=((2, 7),) -> size 5
  NewShape = [2,3], % size 6
  _ = Start.reshape(NewShape).

% --- Symbolic ---
test('symbolic contiguous', []) :-
  W in 1..10,
  Start = view{shape:[W,4], strides:[4,1], offset:0, mask:_},
  W4 #= W*4,
  NewShape = [W4],
  Expected = view{shape:NewShape, strides:[1], offset:0, mask:_},
  Start.reshape(NewShape) = Expected.

test('symbolic non-contiguous fail', [fail]) :-
  W in 1..10,
  Start = view{shape:[4,W], strides:[W,1], offset:0, mask:_},
  W4 #= W*4,
  NewShape = [W4],
  _ = Start.reshape(NewShape).

test('symbolic no-op', []) :-
  W in 1..10,
  Start = view{shape:[4,W], strides:[1,4], offset:0, mask:_},
  NewShape = [4,W],
  Start.reshape(NewShape) = Start.

:- end_tests(reshape).
