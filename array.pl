:- module(array, []).

:- use_module(library(clpfd)).

view:_.from_shape(Shape) := View :-
   shape_strides(Shape, Strides),
   shape_mask(Shape, Mask),
   View = view{shape: Shape, strides: Strides, mask: Mask, offset: 0}.

M.default() := Dict :-
   Dict = M.default([]).
M.default(Options) := Dict :-
   dict_options(M, MOptions),
   merge_options(Options, MOptions, Merged),
   option(dtype(DType), Merged, float),
   option(device(Device), Merged, prolog),
   Dict = array{views: [], dtype:DType, device:Device, data: _}.

M.empty(Shape) := Dict :-
   Dict = M.empty(Shape, []).
M.empty(Shape, Options) := Dict :-
   shape_size(Shape, Size),
   Dict = M.default(Options).push(buffer(Size)).

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

mul(A, B, C, B) :-
   C #= A*B.
shape_strides([_ | Shape], [Stride | Strides]) :-
   shape_strides(Strides, Shape, Stride).
shape_strides([], [], 1).
shape_strides([Stride | Strides], [Dim | Shape], ParentStride) :-
   ParentStride #= Stride*Dim,
   shape_strides(Strides, Shape, Stride).

:- begin_tests(strides).

test('strides_1') :-
   shape_strides([_], [1]).
test('strides_2') :-
   shape_strides([2, 3], [3, 1]).
test('strides_3') :-
   shape_strides([2, 3, 4], [12, 4, 1]).

:- end_tests(strides).
