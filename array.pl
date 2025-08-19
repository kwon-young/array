:- module(array, []).

:- use_module(library(clpfd)).
:- use_module(library(pairs)).

view:_.from_shape(Shape) := View :-
   shape_strides(Shape, Strides),
   shape_mask(Shape, Mask),
   View = view{shape: Shape, strides: Strides, mask: Mask, offset: 0}.

view:M.reshape(Shape) := Dict :-
   merge_dims(M.zip(), MergedPairs),
   Dict = M.put([shape: Shape, strides: _, mask: _]),
   merge_dims(Dict.zip(), MergedPairs).

view:M.zip() := Zip :-
   maplist([Dim, Stride, Mask, Dim-Stride-Mask]>>true, M.shape, M.strides, M.mask, Zip).
view:M.size() := Size :-
   shape_size(M.shape, Size).

M.default() := Dict :-
   Dict = M.default([]).
M.default(Options) := Dict :-
   dict_options(M, MOptions),
   merge_options(Options, MOptions, Merged),
   option(dtype(DType), Merged, float),
   option(device(Device), Merged, prolog),
   Dict = array{views: [], dtype:DType, device:Device, data: _}.

M.push(buffer(Size)) := Dict :-
   Dict = M.push_view(view{}.from_shape([Size])).push_op(buffer(Size)).
M.push_op(Op) := Dict :-
   Dict = M.put([id: _Id, op: Op]).
M.push_view(View) := Dict :-
   Dict = M.put([views: [View | M.views]]).
M.pop_view(View) := Dict :-
   M.views = [View | Views],
   Dict = M.put([views: Views]).
M.replace_view(View) := Dict :-
   Dict = M.pop_view(_).push_view(View).
M.view() := View :-
   M.views = [View | _].
M.size() := Size :-
   Size = M.view().size().
M.shape() := Shape :-
   Shape = M.view().shape.

M.empty(Shape) := Dict :-
   Dict = M.empty(Shape, []).
M.empty(Shape, Options) := Dict :-
   shape_size(Shape, Size),
   Dict = M.default(Options).push(buffer(Size)).reshape(Shape).

M.reshape(Shape) := Dict :-
   (  shape_size(Shape, M.size())
   -> (  View = M.view().reshape(Shape)
      -> Dict = M.replace_view(View)
      ;  Dict = M.push_view(view{}.from_shape(Shape))
      )
   ;  domain_error(M.shape(), Shape)
   ).

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
   maplist([Dim, 0-Dim]>>true, Shape, Mask).

shape_strides([], []).
shape_strides([_ | Shape], [HeadStride | Strides]) :-
   foldl([Dim, Stride, ParentStride, Stride]>>(ParentStride #= Dim*Stride),
         Shape, Strides, HeadStride, 1).

:- table merge_dims/2.

merge_dims([], [1-1-(0-1)]).
merge_dims([H | T], MergedPairs) :-
   merge_dims_acc(T, H, MergedPairs).

merge_dims_acc([], Acc, [Acc]).
merge_dims_acc([Dim-Stride-(Min-Max) | T], AccDim-AccStride-(AccMin-AccMax), Merged) :-
   mask(Dim, Min-Max),
   mask(AccDim, AccMin-AccMax),
   AccStride #= Dim * Stride 
      #/\ (
             (Min #= 0 #/\ Max #= Dim #/\ AccMin #= 0 #/\ AccMax #= AccDim)
         #\/ (Max - Min #= 1 #/\ AccMax - AccMin #= 1)
      )
      #<==> C,
   merge_dims_acc(C, [Dim-Stride-(Min-Max) | T], AccDim-AccStride-(AccMin-AccMax), Merged).

merge_dims_acc(1, [Dim-Stride-(Min-Max) | T], AccDim-_-(AccMin-AccMax), Merged) :-
   NewAccDim #= AccDim * Dim,
   NewMin #= AccMin*AccDim + Min,
   NewMax #= (AccMax-1)*Dim + Max,
   merge_dims_acc(T, NewAccDim-Stride-(NewMin-NewMax), Merged).
merge_dims_acc(0, [H | T], Acc, [Acc | MergedTail]) :-
   merge_dims_acc(T, H, MergedTail).

mask(Dim, Min-Max) :-
   Min #>= 0,
   Max #>= 0,
   Min #=< Dim,
   Max #=< Dim,
   Max #>= Min.

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
   view{}.from_shape([5]) = view{shape: [5], strides: [1], mask: [0-5], offset: 0},
   view{}.from_shape([2, 3]) = view{shape: [2, 3], strides: [3, 1], mask: [0-2, 0-3], offset: 0},
   view{}.from_shape([2, 3, 4]) = view{shape: [2, 3, 4], strides: [12, 4, 1], mask: [0-2, 0-3, 0-4], offset: 0}.

:- end_tests(view).

:- begin_tests(reshape).

% ===== SUCCESSFUL RESHAPES =====
% --- Contiguous ---
test('contiguous merge') :-
  Start = view{}.from_shape([2,3,4]),
  NewShape = [6,4],
  Reshaped = Start.reshape(NewShape),
  Reshaped.shape == NewShape,
  Reshaped.strides == [4,1],
  Reshaped.mask == [0-6, 0-4].

test('contiguous split') :-
  Start = view{}.from_shape([24]),
  NewShape = [2,3,4],
  Reshaped = Start.reshape(NewShape),
  Reshaped.shape == NewShape,
  Reshaped.strides == [12, 4, 1],
  Reshaped.mask == [0-2, 0-3, 0-4].

test('contiguous to scalar') :-
  Start = view{}.from_shape([1]),
  NewShape = [],
  Reshaped = Start.reshape(NewShape),
  Reshaped.shape == NewShape,
  Reshaped.strides == [],
  Reshaped.mask == [].

test('scalar to contiguous') :-
  Start = view{}.from_shape([]),
  NewShape = [1,1,1],
  Reshaped = Start.reshape(NewShape),
  Reshaped.shape == NewShape,
  Reshaped.strides == [1,1,1],
  Reshaped.mask == [0-1, 0-1, 0-1].

test('contiguous with ones') :-
  Start = view{}.from_shape([1,10,1]),
  NewShape = [10],
  Reshaped = Start.reshape(NewShape),
  Reshaped.shape == NewShape,
  Reshaped.strides == [1],
  Reshaped.mask == [0-10].

% --- Non-contiguous (from expand, permute) ---
test('split expanded dim') :-
  Start = view{}.from_shape([10,10]).put(strides, [1,0]),
  NewShape = [10,2,5],
  Reshaped = Start.reshape(NewShape),
  Reshaped.shape == NewShape,
  Reshaped.strides == [1,0,0],
  Reshaped.mask == [0-10, 0-2, 0-5].

test('split other expanded dim') :-
  Start = view{}.from_shape([10,10]).put(strides, [0,1]),
  NewShape = [10,5,2],
  Reshaped = Start.reshape(NewShape),
  Reshaped.shape == NewShape,
  Reshaped.strides == [0,2,1],
  Reshaped.mask == [0-10, 0-5, 0-2].

test('merge after permute') :-
  Start = view{}.from_shape([3,4,2]).put(strides, [4,1,12]),
  NewShape = [12,2],
  Reshaped = Start.reshape(NewShape),
  Reshaped.shape == NewShape,
  Reshaped.strides == [1,12],
  Reshaped.mask == [0-12, 0-2].

test('double permute with merge', [fail]) :-
  Start = view{}.from_shape([4,4,4]).put(strides, [1,16,4]),
  NewShape = [16,4],
  Reshaped = Start.reshape(NewShape),
  Reshaped.shape == NewShape,
  Reshaped.strides == [4,1],
  Reshaped.mask == [0-16, 0-4].

% --- Masked ---
test('reshape masked view', [fail]) :-
  Start = view{}.from_shape([10]).put(mask, [2-8]),
  NewShape = [3,2],
  Reshaped = Start.reshape(NewShape),
  Reshaped.shape == NewShape,
  Reshaped.strides == [2,1],
  Reshaped.mask == [0-3, 0-2],
  Reshaped.offset == 2.

test('reshape with offset') :-
  Start = view{}.from_shape([6]).put(offset, 2),
  NewShape = [2,3],
  Reshaped = Start.reshape(NewShape),
  Reshaped.shape == NewShape,
  Reshaped.strides == [3,1],
  Reshaped.mask == [0-2, 0-3],
  Reshaped.offset == 2.

test('masked with pad no-op reshape') :-
  Start = view{}.from_shape([14]).put([offset: -2, mask:[2-12]]),
  NewShape = [14],
  Reshaped = Start.reshape(NewShape),
  Reshaped.shape == NewShape,
  Reshaped.strides == [1],
  Reshaped.mask == [2-12],
  Reshaped.offset == -2.

% --- Zero shapes ---
test('zero shape to zero shape') :-
  Start = view{}.from_shape([2,0,4]).put(strides, [0,4,1]),
  NewShape = [0,3,1],
  Reshaped = Start.reshape(NewShape),
  Reshaped.shape == NewShape,
  Reshaped.strides == [3,1,1],
  Reshaped.mask == [0-0, 0-3, 0-1].

test('zero shape with ones') :-
  Start = view{}.from_shape([1,10,0]).put(strides, [0,0,1]),
  NewShape = [0],
  Reshaped = Start.reshape(NewShape),
  Reshaped.shape == NewShape,
  Reshaped.strides == [1],
  Reshaped.mask == [0-0].

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
  Start = view{shape:[10], strides:[1], offset:0, mask:[2-7]}, % mask=((2, 7),) -> size 5
  NewShape = [2,3], % size 6
  _ = Start.reshape(NewShape).

% --- Symbolic ---
test('symbolic contiguous', []) :-
  W in 1..10,
  Start = view{}.from_shape([W,4]),
  W4 #= W*4,
  NewShape = [W4],
  Reshaped = Start.reshape(NewShape),
  Reshaped.shape == NewShape,
  Reshaped.strides == [1],
  Reshaped.mask = [0-W4].

test('symbolic non-contiguous fail', [fail]) :-
  W in 1..10,
  Start = view{shape:[4,W], strides:[1,W], offset:0, mask:[0-3, 0-W]},
  W4 #= W*4,
  NewShape = [W4],
  _ = Start.reshape(NewShape).

test('symbolic no-op', []) :-
  W in 1..10,
  Start = view{}.from_shape([4,W]).put(strides, [1,4]),
  NewShape = [4,W],
  Reshaped = Start.reshape(NewShape),
  Reshaped.shape == NewShape,
  Reshaped.strides == [1,4],
  Reshaped.mask == [0-4, 0-W].

test('single element mask', []) :-
   Start = view{}.from_shape([4]).put([mask:[1-2]]),
   NewShape = [2, 2],
   Reshaped = Start.reshape(NewShape),
   Reshaped.shape == NewShape,
   Reshaped.strides == [2, 1],
   Reshaped.mask == [0-1, 1-2].

:- end_tests(reshape).

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

test('reshape with mismatched size fails', [throws(error(domain_error(_,_),_))]) :-
  A = array{}.empty([2,3]),
  % New shape has size 9, original has size 6.
  _ = A.reshape([3,3]).

:- end_tests(array_reshape).

:- begin_tests(array_empty).

test('create empty array') :-
  A = array{}.empty([2,3], [dtype(float), device(prolog)]),
  A.shape() == [2,3],
  A.dtype == float,
  A.device == prolog,
  A.op == buffer(6),
  length(A.views, 1),
  A.view().shape == [2,3].

:- end_tests(array_empty).
