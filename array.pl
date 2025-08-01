:- module(array, [
   op(600, fy, :),
   op(600, fy, ::),
   op(600, xfy, ::)
]).
:- reexport(library(type_ndarray), except([ndarray/1])).

:- use_module(library(clpfd), except([sum/3])).
:- use_module(library(dcg/basics)).
:- use_module(library(dcg/high_order)).
:- use_module(library(type_ndarray)).
:- use_module(library(arithmetic_types)).

:- arithmetic_function([]/1).         % block indexing and slicing
:- arithmetic_function([]/2).
:- arithmetic_function('.+'/2).       % numeric array addition
:- arithmetic_function('.-'/1).       % numeric array unary minus
:- arithmetic_function('.-'/2).       % numeric array subtraction
:- arithmetic_function('.*'/2).       % numeric array product
:- arithmetic_function('./'/2).       % numeric array division
:- arithmetic_function('.**'/2).      % numeric array power
:- arithmetic_function('.@'/2).       % dot product of two vectors/matrices

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

mutable(Data, Options) :-
   compound_name_arity(Data, data, Size),
   (  option(mutable(false), Options, false)
   -> arg(Size, Data, false)
   ;  true
   ).

M.contiguous() := Contiguous :-
   Contiguous = contiguous(M.shape, M.strides, Contiguous).
M.size() := Size :-
   shape_size(M.shape, Size).
M.to(Device) := Dict :-
   Dict = M.put([device: Device]).
M.arg_offset(Offset) := I :-
   I is (Offset mod M.buffersize) + M.offset + 1.
M.arg_(Offset) := V :-
   arg(M.arg_offset(Offset), M.data, V).
M.data() := Data :-
   Data = M.data,
   (  var(Data)
   -> call(M.delayed)
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
   Dict = array{dtype:DType, device:Device, offset:Offset}.

M.empty(Shape) := Dict :-
   Dict = M.empty(Shape, []).
M.empty(Shape, Options) := Dict :-
   same_length(Shape, Strides),
   shape_size(Shape, Size),
   contiguous(Shape, Strides, 1),
   Size1 is Size + 1,
   compound_name_arity(Data, data, Size1),
   mutable(Data, Options),
   Dict = M.default().put([
      data: Data, shape: Shape, strides: Strides, buffersize: Size]).

M.from_list(List) := Dict :-
   Dict = M.from_list(List, []).
M.from_list(List, Options) := Dict :-
   DType = M.get(dtype, _),
   M1 = M.default(),
   shape_type_list(M1.device, Shape, DType, List),
   same_length(Shape, Strides),
   contiguous(Shape, Strides, 1),
   flatten(List, ListData),
   length(ListData, Size),
   append(ListData, [_], ListData1),
   compound_name_arguments(Data, data, ListData1),
   mutable(Data, Options),
   Dict = M1.put([
      data: Data, shape: Shape, strides: Strides, dtype: DType, buffersize: Size]).

M.ones(Shape) := Dict :-
   Dict = M.ones(Shape, []).
M.ones(Shape, Options) := Dict :-
   same_length(Shape, Strides),
   maplist(=(0), Strides),
   Data = data(1, _),
   mutable(Data, Options),
   Dict = M.default().put([
      data: Data, shape: Shape, strides: Strides, buffersize: 1]).

M.arange(Start, Stop, Step, Options) := Dict :-
   Size is ceil((Stop - Start) / Step),
   Dict = M.empty([Size], Options),
   foldlarray({Step}/[Prev, Prev, Next]>>(Next is Prev + Step), Dict.iter(), Start, _).

M.iter() := Cont :-
   Cont = M.iter_value().
M.iter_value() := Cont :-
   Cont = iterate_value(M).
M.iter_offset() := Cont :-
   Cont = iterate_offset(M).
M.iter_index() := Cont :-
   Cont = iterate_index(M).

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
   (  Next1 == 0, Next2 == 0, Next3
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
   (  Dim == 0
   -> true
   ;  iterate_offset(Shape, Strides, C),
      Dim1 is Dim - 1,
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

% M.is_input() := IsInput :-
%    (  M.data = from_list(_)
%    -> IsInput = true
%    ;  IsInput = false
%    ).
% M.input() := Input :-
%    from_list(Input) = M.data.
%
% M.reshape(Shape) := Dict :-
%    Shape ins 0..sup,
%    shape_size(Shape, M.size),
%    (  compatible_shape_strides(M.shape, M.strides, Shape, Strides)
%    -> Data = view(M), M1 = M
%    ;  Data = +(M),
%       same_length(Shape, Strides),
%       contiguous(Shape, Strides, 1),
%       product(Shape, #=, BufferSize),
%       M1 = M.put([offset=0, buffer=_, buffersize=BufferSize])
%    ),
%    Dict = M1.put([data=Data, shape=Shape, strides=Strides]).
%
% M.t() := Dict :-
%    reverse(M.shape, Shape),
%    reverse(M.strides, Strides),
%    Dict = M.put([data=view(M), shape=Shape, strides=Strides]).
%
% take_nth0(Index, Value, L, R) :-
%    nth0(Index, L, Value, R).
% put_nth0(Index, Value, R, L) :-
%    nth0(Index, L, Value, R).
%
% replace_nth0(Index, Old, New) -->
%    take_nth0(Index, Old),
%    put_nth0(Index, New).
%
% swap(I1, I2) -->
%    replace_nth0(I1, V1, V2),
%    replace_nth0(I2, V2, V1).
%
% M.swapaxes(Axis1, Axis2) := Dict :-
%    swap(Axis1, Axis2, M.shape, Shape),
%    swap(Axis1, Axis2, M.strides, Strides),
%    Dict = M.put([data=view(M), shape=Shape, strides=Strides]).
%
% M.ndim() := NDim :-
%    length(M.shape, NDim).
%
% M.index(Index) := Dict :-
%    index_shape(Index, M.shape, Shape),
%    index_shape_strides_offset(Index, M.shape, M.strides, Strides, NewOffset),
%    Offset #= M.offset + NewOffset,
%    shape_size(Shape, Size),
%    Dict = M.put([data=index(M), shape=Shape, strides=Strides, offset=Offset, size=Size]).
%
% positive_index(Index, Dim, PositiveIndex) :-
%    (  Index == sup
%    -> I = Dim
%    ;  I = Index
%    ),
%    I #>= Dim #<==> OverTheEnd,
%    PositiveIndex #= max(min(I, Dim-1), -Dim) mod Dim + OverTheEnd.
%
% start_end_stop(Start:End:Step, Start1, End1, Step1) =>
%    Start = Start1,
%    End = End1,
%    Step = Step1.
% start_end_stop(:, Start1, End1, Step1) =>
%    0 = Start1,
%    sup = End1,
%    1 = Step1.
% start_end_stop(:End, Start1, End1, Step1) =>
%    0 = Start1,
%    End = End1,
%    1 = Step1.
% start_end_stop(:End:Step, Start1, End1, Step1) =>
%    0 = Start1,
%    End = End1,
%    Step = Step1.
% start_end_stop(Start:sup, Start1, End1, Step1) =>
%    Start = Start1,
%    sup = End1,
%    1 = Step1.
% start_end_stop(Start:End, Start1, End1, Step1) =>
%    Start = Start1,
%    End = End1,
%    1 = Step1.
% start_end_stop(::Step, Start1, End1, Step1) =>
%    0 = Start1,
%    sup = End1,
%    Step = Step1.
% start_end_stop(Start::Step, Start1, End1, Step1) =>
%    Start = Start1,
%    sup = End1,
%    Step = Step1.
% start_end_stop(List, Start, End, Step), is_list(List), list_step(List, Step) =>
%    List = [Start | _],
%    last(List, Last),
%    End #= Last + Step.
% start_end_stop(_, _, _, _) =>
%    fail.
%
% list_step([H | T], Step) :-
%    foldl({Step}/[A, B, A]>>(Step #= A - B), T, H, _).
%
% index_shape_strides_offset([], _Shape, Strides, NewStrides, Offset) =>
%    NewStrides = Strides,
%    Offset = 0.
% index_shape_strides_offset(
%       [I | Index], [Dim | Shape], [Stride | Strides], NewStrides, Offset
%       ), start_end_stop(I, Start, _End, Step) =>
%    NewStride #= Stride * Step,
%    NewStrides = [NewStride | NewStridesRest],
%    Step #< 0 #<==> Reverse,
%    Offset #= Reverse * (Dim - 1) * Stride + Start * Stride + SubOffset,
%    index_shape_strides_offset(Index, Shape, Strides, NewStridesRest, SubOffset).
% index_shape_strides_offset(
%       [I | Index], [Dim | Shape], [Stride | Strides], NewStrides, Offset),
%       (var(I) ; integer(I)) =>
%    I #>= -Dim,
%    I #< Dim,
%    positive_index(I, Dim, PositiveI),
%    Offset #= PositiveI * Stride + SubOffset,
%    index_shape_strides_offset(Index, Shape, Strides, NewStrides, SubOffset).
% index_shape_strides_offset(
%       [I | Index], [_Dim | Shape], [Stride | Strides], NewStrides, Offset),
%       is_list(I) =>
%    A @= array{dtype: int64}.from_list(I) * Stride,
%    NewStrides = [A | NewStridesRest],
%    index_shape_strides_offset(Index, Shape, Strides, NewStridesRest, Offset).
% index_shape_strides_offset(_, _, _, _, _) =>
%    fail.
%
% index_shape([], Shape, NewShape) =>
%    NewShape = Shape.
% index_shape([I | Index], [Dim | Shape], NewShape), start_end_stop(I, Start, End, Step) =>
%    positive_index(Start, Dim, PositiveStart),
%    positive_index(End, Dim, PositiveEnd),
%    Size #= max(0, PositiveEnd - PositiveStart),
%    NewDim #= Size div abs(Step) + min(1, Size mod abs(Step)),
%    NewShape = [NewDim | NewShapeRest],
%    index_shape(Index, Shape, NewShapeRest).
% index_shape([I | Index], [Dim | Shape], NewShape), is_list(I) =>
%    maplist(dim_index(Dim), I),
%    length(I, NewDim),
%    NewShape = [NewDim | NewShapeRest],
%    index_shape(Index, Shape, NewShapeRest).
% index_shape([I | Index], [Dim | Shape], NewShape) =>
%    dim_index(Dim, I),
%    index_shape(Index, Shape, NewShape).
%
% dim_index(Dim, I) :-
%    I #>= -Dim,
%    I #< Dim.
%
% promote(X, Y), is_dict(X, array) =>
%    X = Y.
% promote(X, Y), integer(X) =>
%    Y = array{data: data(X), shape: [], strides: [], offset: 0,
%              device: c, dtype: int64, size: 1, buffer: _, buffersize: 1}.
%
% broadcast(Arrays, NewArrays) :-
%    maplist(promote, Arrays, Arrays1),
%    maplist(get_dict(shape), Arrays1, Shapes),
%    maplist(get_dict(strides), Arrays1, Strides),
%    broadcast(Shapes, Strides, NewShape, NewStrides),
%    product(NewShape, #=, Size),
%    maplist(
%       {NewShape, Size}/[Stride, Array, NewArray]>>(
%          put_dict([shape=NewShape, strides=Stride, size=Size, data=view(Array)],
%                   Array, NewArray)),
%       NewStrides, Arrays1, NewArrays).
%
% broadcast(Shapes, Strides, NewShape, NewStrides) :-
%    maplist(length, Shapes, Lengths),
%    max_list(Lengths, L),
%    maplist(pad(1, L), Shapes, PaddedShapes),
%    maplist(pad(0, L), Strides, PaddedStrides),
%    maplist(reverse, PaddedShapes, RPaddedShapes),
%    maplist(reverse, PaddedStrides, RPaddedStrides),
%    same_length(RPaddedShapes, RPairs),
%    maplist(pairs_keys_values, RPairs, RPaddedShapes, RPaddedStrides),
%    transpose(RPairs, RPairsT),
%    maplist(broadcast_pairs, RPairsT, RNewShape, RNewStridesT),
%    transpose(RNewStridesT, RNewStrides),
%    maplist(reverse, RNewStrides, NewStrides),
%    reverse(RNewShape, NewShape).
%
% pad(V, Length, ShapeIn, ShapeOut) :-
%    length(ShapeOut, Length),
%    length(ShapeIn, InLength),
%    PadLength is Length - InLength,
%    length(Padding, PadLength),
%    append(Padding, ShapeIn, ShapeOut),
%    maplist(=(V), Padding).
%   
% broadcast_pairs(Pairs, D, Strides) :-
%    foldl(broadcast_shape, Pairs, 1, D),
%    maplist(broadcast_stride(D), Pairs, Strides).
%
% broadcast_shape(D2-_, D1, D) :-
%    D1 #\= 1 #/\ D1 #= D
%    #\ D1 #= 1 #/\ D2 #= D,
%    D2 #\= 1 #/\ D2 #= D
%    #\ D2 #= 1 #/\ D1 #= D.
% broadcast_stride(D, D1-S1, S2) :-
%    D #= D1 #/\ S1 #= S2
%    #\ D #\= D1 #/\ S2 #= 0.
%
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
% squeeze_(Axis) -->
%    take_nth0(Axis, Dim-_),
%    (  {Dim = 1}
%    -> []
%    ;  {domain_error(1, Dim)}
%    ).
%
% M.squeeze(Axis) := Dict :-
%    sort(0, @>=, Axis, SortedAxis),
%    pairs_keys_values(Pairs, M.shape, M.strides),
%    phrase(sequence(squeeze_, SortedAxis), Pairs, NewPairs),
%    pairs_keys_values(NewPairs, NewShape, NewStrides),
%    Dict = M.put([shape=NewShape, strides=NewStrides, data=view(M)]).
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
