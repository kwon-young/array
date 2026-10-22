:- module(view, [replace_nth0/4, lpad/4]).

:- use_module(library(clpfd), except([transpose/2, sum/3])).

% Creation
% ========
_.from_shape(Shape) := View :-
   shape_strides(Shape, Strides),
   shape_mask(Shape, Mask),
   View = view{shape: Shape, strides: Strides, mask: Mask, offset: 0}.

M.with_shape(Shape) := View :-
   View = M.put([shape: Shape, strides: _, mask: _]).

M.with_zip(Zip) := View :-
   same_length(Zip, Shape),
   View = M.with_shape(Shape),
   Zip = View.zip().

% Movement
% ========

M.reshape(Shape) := Dict :-
   (  shape_size(Shape, M.size())
   -> merge_dims(M.zip(), MergedPairs),
      Dict = M.with_shape(Shape),
      shape_strides(Shape, RowMajor),
      maplist(unit_stride, Shape, RowMajor, Dict.strides),
      merge_dims(Dict.zip(), MergedPairs)
   ;  domain_error(M.shape, Shape)
   ).

% The stride of a new dim of size 1 is never used: it is row-major.
unit_stride(Dim, RowMajor, Stride) :-
   (Dim #= 1) #==> (Stride #= RowMajor).

:- table merge_dims/2.

merge_dims([], [1-1-(0-1)]).
merge_dims([H | T], MergedPairs) :-
   merge_dims(T, H, MergedPairs).

% A dim of size 1 of data has the single index 0: its stride is never used,
% so it drops out of the merged form whatever its stride. A view of such
% dims only merges as a scalar.
merge_dims([], Acc, Merged) :-
   unit_dim(Acc, Unit),
   merge_last(Unit, Acc, Merged).
merge_dims([H | T], Acc, Merged) :-
   unit_dim(H, UnitH),
   merge_next(UnitH, H, T, Acc, Merged).

merge_last(1, _, [1-1-(0-1)]).
merge_last(0, Acc, [Acc]).

% H drops out.
merge_next(1, _, T, Acc, Merged) :-
   merge_dims(T, Acc, Merged).
merge_next(0, H, T, Acc, Merged) :-
   unit_dim(Acc, UnitAcc),
   merge_acc(UnitAcc, H, T, Acc, Merged).

% Acc drops out: it is a dim of size 1 that only dims of size 1 preceded.
merge_acc(1, H, T, _, Merged) :-
   merge_dims(T, H, Merged).
merge_acc(0, H, T, Acc, Merged) :-
   merge_pair(H, T, Acc, Merged).

merge_pair(Dim-Stride-(Min-Max), T, AccDim-AccStride-(AccMin-AccMax), Merged) :-
   (  full_mask(Dim, Min-Max), full_mask(AccDim, AccMin-AccMax)
   ;  single_element_mask(Dim, Min-Max), single_element_mask(AccDim, AccMin-AccMax)
   ),
   AccStride #= Dim * Stride,
   NewAccDim #= AccDim * Dim,
   NewMin #= AccMin*Dim + Min,
   NewMax #= (AccMax-1)*Dim + Max,
   merge_dims(T, NewAccDim-Stride-(NewMin-NewMax), Merged).
merge_pair(H, T, Acc, [Acc | MergedTail]) :-
   H = Dim-Stride-_,
   Acc = _-AccStride-_,
   AccStride #\= Dim * Stride,
   merge_dims(T, H, MergedTail).

unit_dim(Dim-_-(Min-Max), Unit) :-
   Unit #<==> (Dim #= 1 #/\ Min #= 0 #/\ Max #= 1).

full_mask(Dim, 0-Dim).
single_element_mask(Dim, Min-Max) :-
   mask(Dim, Min-Max),
   Max - Min #= 1.

M.t() := Dict :-
   Dict = M.transpose().
M.transpose() := Dict :-
   same_length(M.shape, Shape),
   Dict = M.with_shape(Shape),
   reverse(M.zip(), Dict.zip()).

M.swapaxes(Axis1, Axis2) := Dict :-
   swap_nth0(Axis1, Axis2, M.zip(), Zip),
   Dict = M.with_zip(Zip).

M.permute(Axes) := Dict :-
   In = M.zip(),
   maplist({In}/[I, O]>>nth0(I, In, O), Axes, Out),
   Dict = M.with_zip(Out).

M.expand(Shape) := Dict :-
   Dict = M.broadcast_view(Shape).

M.unsqueeze(Axis) := Dict :-
   nth0(Axis, NewShape, 1, M.shape),
   Dict = M.reshape(NewShape).

M.pad(Padding) := Dict :-
   maplist(pad_dim, Padding, M.zip(), Zip, Offsets),
   clpfd:sum(Offsets, #=, PaddingOffset),
   Offset #= M.offset + PaddingOffset,
   Dict = M.with_zip(Zip).put(offset, Offset).
pad_dim(Low-High, Dim1-Stride-(Min1-Max1), Dim2-Stride-(Min2-Max2), Offset) :-
   Dim2 #= Dim1 + Low + High,
   Min2 #= Min1 + Low,
   Max2 #= Max1 + Low,
   Offset #= -(Low*Stride).

M.shrink(Shrink) := Dict :-
   foldl(shrink_dim, Shrink, M.zip(), Zip, M.offset, Offset),
   Dict = M.with_zip(Zip).put(offset, Offset).
shrink_dim(Start-End, Dim-Stride-Mask0, Dim1-Stride-Mask, In, Out) :-
   mask(Dim, Start-End),
   Dim1 #= (End - Start),
   shrink_mask(Start, Dim1, Mask0, Mask),
   Out #= In + Start*Stride.

% The valid part of a shrunk dim: its old mask, shifted by Start and clipped
% to the new dim. 0-0 when the shrink only keeps padding.
shrink_mask(Start, Dim1, Min-Max, Min1-Max1) :-
   Low #= max(0, min(Dim1, Min - Start)),
   High #= max(0, min(Dim1, Max - Start)),
   NonEmpty #<==> (High #> Low),
   Min1 #= Low*NonEmpty,
   Max1 #= High*NonEmpty.

:- table broadcast_view/3.

In.broadcast_view(Shape) := Out :-
   length(Shape, N),
   lpad(N, 1-0-(0-1), In.zip(), Zip),
   Out = In.with_shape(Shape),
   maplist(broadcast_, Shape, Zip, Out.zip()).

broadcast_(1, Pair, Pair) :-
   Pair = Dim-_-_,
   Dim #\= 1.
broadcast_(Dim, 1-_-(0-Max), Dim-0-(0-NewMax)) :-
   Dim #\= 1,
   NewMax #= Max * Dim. % Max is either 0 or 1
broadcast_(Dim, Dim-Stride-Mask, Dim-Stride-Mask).

% Properties
% ==========
M.size() := Size :-
   shape_size(M.shape, Size).

M.ndim() := NDim :-
   length(M.shape, NDim).

% As in numpy, the elements are one row-major block, from any offset: the
% strides are row-major but on dims of size 1, and every element is valid.
M.is_contiguous() := Res :-
   (  shape_strides(M.shape, RowMajor),
      maplist(contiguous_stride, M.shape, RowMajor, M.strides),
      shape_mask(M.shape, M.mask)
   -> Res = true
   ;  Res = false
   ).

% The only index of a dim of size 1 is 0: its stride is never used.
contiguous_stride(Dim, RowMajor, Stride) :-
   (Dim #= 1) #\/ (RowMajor #= Stride).

% Helpers
% =======
M.zip() := Zip :-
   maplist([Dim, Stride, Mask, Dim-Stride-Mask]>>true, M.shape, M.strides, M.mask, Zip).

View.index_expr(Index) := FlatIndex :-
   foldl([I, Stride, Sum, Sum+I*Stride]>>true,
         Index, View.strides, View.offset, FlatIndex).

View.reverse_index_expr(FlatIndex) := Index :-
   shape_strides(View.shape, Strides),
   foldl([Stride, Flat // Stride, Flat, Flat mod Stride]>>true,
         Strides, Index, FlatIndex, _).

View.valid_expr(Index) := ValidExpr :-
   foldl(valid_dim, View.shape, Index, View.mask, true, ValidExpr).
valid_dim(Dim, I, Min-Max, PrevAST, AST) :-
   (  Min = 0
   -> MinAST = true
   ;  MinAST = (Min =< I)
   ),
   (  Max = Dim
   -> MaxAST = true
   ;  MaxAST = (I < Max)
   ),
   mkconj(MinAST, MaxAST, DimAST),
   mkconj(PrevAST, DimAST, AST).

% Utilities
% =========
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
   maplist(dim_mask, Shape, Mask).
dim_mask(Dim, 0-Dim).

shape_strides([], []).
shape_strides([_ | Shape], [HeadStride | Strides]) :-
   foldl([Dim, Stride, ParentStride, Stride]>>(ParentStride #= Dim*Stride),
         Shape, Strides, HeadStride, 1).

mask(Dim, Min-Max) :-
   Min #>= 0,
   Max #>= 0,
   Min #=< Dim,
   Max #=< Dim,
   Max #>= Min.

replace_nth0(New, N, In, Out) :-
   replace_nth0(_, New, N, In, Out).
replace_nth0(Old, New, N, In, Out) :-
   nth0(N, In, Old, Tmp),
   nth0(N, Out, New, Tmp).

swap_nth0(N1, N2, In, Out) :-
   replace_nth0(V1, V2, N1, In, Tmp),
   replace_nth0(V2, V1, N2, Tmp, Out).

lpad(N, Value, L, PadL) :-
   length(PadL, N),
   once(append(Pad, L, PadL)),
   maplist(=(Value), Pad).

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

:- begin_tests(shrink).

padded(View) :-
   View = view{}.from_shape([2]).pad([1-1]).

test('shrink keeps the padding of the start', [timeout(5)]) :-
   padded(Padded),
   View = Padded.shrink([0-2]),
   view{shape: Shape, mask: Mask, offset: Offset} :< View,
   Shape == [2],
   Mask == [1-2],
   Offset == -1.

test('shrink keeps the padding of the end', [timeout(5)]) :-
   padded(Padded),
   View = Padded.shrink([2-4]),
   view{shape: Shape, mask: Mask, offset: Offset} :< View,
   Shape == [2],
   Mask == [0-1],
   Offset == 1.

test('shrink inside the padding gives an empty mask', [timeout(5)]) :-
   Padded = view{}.from_shape([2]).pad([2-0]),
   View = Padded.shrink([0-1]),
   view{mask: Mask} :< View,
   Mask == [0-0].

test('shrink after the data gives an empty mask', [timeout(5)]) :-
   Padded = view{}.from_shape([2]).pad([0-2]),
   View = Padded.shrink([3-4]),
   view{mask: Mask} :< View,
   Mask == [0-0].

test('shrink of an unpadded dim keeps a full mask', [timeout(5)]) :-
   View = view{}.from_shape([4]).shrink([1-3]),
   view{mask: Mask, offset: Offset} :< View,
   Mask == [0-2],
   Offset == 1.

test('shrink of a symbolic dim keeps a full mask', [timeout(5)]) :-
   W in 1..10,
   View = view{}.from_shape([W]).shrink([0-W]),
   view{mask: Mask} :< View,
   W = 5,
   Mask == [0-5].

test('shrink finds the range giving a mask', [timeout(5)]) :-
   Padded = view{shape: [6], strides: [1], mask: [1-5], offset: -1},
   findall(Start-End,
           (  [Start, End] ins 0..6,
              View = Padded.shrink([Start-End]),
              view{shape: [2], mask: [1-2]} :< View,
              label([Start, End])
           ),
           Ranges),
   Ranges == [0-2].

:- end_tests(shrink).

:- begin_tests(contiguous).

test('a view from an offset is contiguous', [timeout(5)]) :-
   View = view{}.from_shape([3]).shrink([1-3]),
   View.is_contiguous() == true.

test('a row of a matrix is contiguous', [timeout(5)]) :-
   View = view{}.from_shape([2, 3]).shrink([1-2, 0-3]),
   View.is_contiguous() == true.

test('a dim of size 1 has any stride', [timeout(5)]) :-
   View = view{shape: [1, 3], strides: [7, 1], mask: [0-1, 0-3], offset: 0},
   View.is_contiguous() == true.

test('a dim with another stride is contiguous only of size 1', [timeout(5)]) :-
   D in 1..5,
   View = view{shape: [D, 3], strides: [7, 1], mask: [0-D, 0-3], offset: 0},
   View.is_contiguous() == true,
   D == 1.

test('a column of a matrix is not contiguous', [timeout(5)]) :-
   View = view{}.from_shape([2, 3]).shrink([0-2, 1-2]),
   View.is_contiguous() == false.

test('a padded view is not contiguous', [timeout(5)]) :-
   View = view{}.from_shape([2]).pad([1-0]),
   View.is_contiguous() == false.

:- end_tests(contiguous).

:- begin_tests(unit_dims).

test('reshape drops a dim of size 1 whatever its stride', [timeout(5)]) :-
   View0 = view{shape: [1, 3], strides: [7, 1], mask: [0-1, 0-3], offset: 0},
   View = View0.reshape([3]),
   view{shape: Shape, strides: Strides, mask: Mask} :< View,
   Shape == [3],
   Strides == [1],
   Mask == [0-3].

test('reshape gives a new dim of size 1 its row-major stride', [timeout(5)]) :-
   View = view{}.from_shape([3]).reshape([3, 1]),
   view{strides: Strides, mask: Mask} :< View,
   Strides == [1, 1],
   Mask == [0-3, 0-1].

test('reshape of dims of size 1 only is a scalar', [timeout(5)]) :-
   View0 = view{shape: [1, 1], strides: [7, 5], mask: [0-1, 0-1], offset: 2},
   View = View0.reshape([]),
   view{shape: Shape, offset: Offset} :< View,
   Shape == [],
   Offset == 2.

test('reshape makes an unknown mask of size 1 a mask of data', [timeout(5)]) :-
   View0 = view{shape: [1, 3], strides: [3, 1], mask: [Mask, 0-3], offset: 0},
   _ = View0.reshape([3]),
   Mask == 0-1.

test('reshape keeps a dim of size 1 of padding', [fail, timeout(5)]) :-
   Padded = view{}.from_shape([2]).pad([1-0]),
   Shrunk = Padded.shrink([0-1]),
   _ = Shrunk.reshape([]).

:- end_tests(unit_dims).

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
test('reshape masked view', [throws(error(domain_error(_,_),_))]) :-
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

test('masked split unaligned', [throws(error(domain_error(_,_),_))]) :-
  Start = view{shape:[10], strides:[1], offset:0, mask:[2-7]}, % mask=((2, 7),) -> size 5
  NewShape = [2,3], % size 6
  _ = Start.reshape(NewShape).

% --- Symbolic ---
test('symbolic contiguous', [nondet]) :-
  W in 1..10,
  Start = view{}.from_shape([W,4]),
  W4 #= W*4,
  NewShape = [W4],
  Reshaped = Start.reshape(NewShape),
  Reshaped.shape == NewShape,
  Reshaped.strides == [1],
  Reshaped.mask = [0-W4].

% only a dim of size 1 drops out whatever its stride
test('symbolic non-contiguous only of size 1', [timeout(5)]) :-
  findall(W,
          (  W in 1..10,
             Start = view{shape:[4,W], strides:[1,W], offset:0, mask:[0-3, 0-W]},
             W4 #= W*4,
             NewShape = [W4],
             _ = Start.reshape(NewShape)
          ),
          Ws),
  Ws == [1].

test('symbolic no-op', [nondet]) :-
  W in 1..10,
  Start = view{}.from_shape([4,W]).put(strides, [1,4]),
  NewShape = [4,W],
  Reshaped = Start.reshape(NewShape),
  Reshaped.shape == NewShape,
  Reshaped.strides == [1,4],
  Reshaped.mask == [0-4, 0-W].

test('single element mask of unequal dims', [timeout(5)]) :-
   Start = view{}.from_shape([6]).put([mask:[2-3]]),
   Reshaped = Start.reshape([3, 2]),
   view{shape: Shape, mask: Mask} :< Reshaped,
   Shape == [3, 2],
   Mask == [1-2, 0-1].

test('single element mask', []) :-
   Start = view{}.from_shape([4]).put([mask:[1-2]]),
   NewShape = [2, 2],
   Reshaped = Start.reshape(NewShape),
   Reshaped.shape == NewShape,
   Reshaped.strides == [2, 1],
   Reshaped.mask == [0-1, 1-2].

:- end_tests(reshape).
