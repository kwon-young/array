:- module(array, [
   op(700, xfx, @=),
   op(400, yfx, @),
   '@='/2
]).

:- use_module(library(lists), except([flatten/2])).
:- use_module(library(clpfd), except([transpose/2, sum/3])).
:- use_module(library(pairs)).
:- use_module(library(dcg/high_order)).
:- use_module(view).
:- use_module(runtime_prolog).

% Creation
% ========
M.default() := Dict :-
   Dict = M.default([]).
M.default(Options) := Dict :-
   dict_options(M, MOptions),
   merge_options(Options, MOptions, Merged),
   option(dtype(DType), Merged, float),
   option(device(Device), Merged, prolog),
   (  option(shape(Shape), Merged)
   -> View = view{}.from_shape(Shape),
      DataSize = View.size(),
      Views = [View]
   ;  Views = []
   ),
   Dict = array{id: _, views: Views, dtype:DType, device:Device, data: _,
                datasize: DataSize, op: true}.

M.empty(Shape) := Dict :-
   Dict = M.empty(Shape, []).
M.empty(Shape, Options) := Dict :-
   Dict = M.default([shape(Shape) | Options]).

M.fromlist(List) := Dict :-
   Dict = M.fromlist(List, []).
M.fromlist(List, Options) := Dict :-
   list_shape(List, Shape),
   flatten(List, Flat),
   M1 = M.empty(Shape, Options),
   Device = M1.device,
   foldl({Device}/[X, In, Out]>>(
      dtype(Device, X, DType),
      common_dtype(Device, DType, In, Out)
   ), Flat, boolean, DType),
   common_dtype_(Device, DType, M1.dtype, M1.dtype),
   (  option(dtype(FinalDType), Options)
   -> M2 = M1.put(dtype, FinalDType)
   ;  M2 = M1.put(dtype, DType)
   ),
   compound_name_arguments(M2.data, data, Flat),
   Dict = M2.
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
   Dict @= M1.cumalu(0, +) + (Start - Step).

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
M.index(Index) := Dict :-
   Dict = M.replace_view(M.view().index(Index)).

M.reshape(Shape) := Dict :-
   (  View = M.view().reshape(Shape)
   -> Dict = M.replace_view(View)
   ;  Dict = M.push_view(view{}.from_shape(Shape))
   ).

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
   Dict = M.replace_view(M.view().squeeze()).
M.squeeze(Axes) := Dict :-
   Dict = M.replace_view(M.view().squeeze(Axes)).

M.unsqueeze(Axis) := Dict :-
   Dict = M.replace_view(M.view().unsqueeze(Axis)).

M.shrink(Shrink) := Dict :-
   Dict = M.replace_view(M.view().shrink(Shrink)).

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
   ;  Dict = M1
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
   shape_list(M.shape(), List),
   flatten(List, Flat),
   compound_name_arguments(M.contiguous().to(prolog).realize().data, data, Flat).
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
   merge_options(Options, [dtype(_)], Merged),
   M1 = M.empty([], Merged),
   dtype(M1.device, Value, M1.dtype),
   Dict = M1.push_op(constant(Value)).
push(rand(Shape, Options), M, Dict) :-
   Dict = M.empty(Shape, Options).push_op(rand).
push(contiguous, M, Dict) :-
   Dict = M.empty(M.shape()).push_op(contiguous(M)).
push(reduce(Op, Axes), M, Dict) :-
   foldl(replace_nth0(1), Axes, M.shape(), Shape),
   sort(Axes, Axes_),
   Dict = M.empty(Shape).push_op(reduce(Op, Axes_, M)).
push(A+B, C) :-
   push(elementwise(+, [A, B]), C).
push(A*B, C) :-
   push(elementwise(*, [A, B]), C).
push(A<B, C) :-
   push(elementwise(<, [A, B]), C).
push(sin(A), C) :-
   push(elementwise(sin, [A]), C).
push(log(A), C) :-
   push(elementwise(log, [A]), C).
push(sqrt(A), C) :-
   push(elementwise(sqrt, [A]), C).
push(elementwise(Op, Args), C) :-
   (  dicts_same_value_for_key(Args, device, Device)
   -> true
   ;  domain_error(device, Args)
   ),
   maplist(get_dict(dtype), Args, DTypes),
   broadcast_dtypes(Device, DTypes, DType),
   broadcast(Args, [H | T]),
   Term =.. [Op, H | T],
   C = H.empty(H.shape(), [dtype(DType)]).push_op(Term).
push(solve(A, B), X) :-
   (  dicts_same_value_for_key([A, B], device, Device)
   -> true
   ;  domain_error(device, [A, B])
   ),
   broadcast_dtypes(Device, [A.dtype, B.dtype], DType),
   X = A.empty(B.shape(), [dtype(DType)]).push_op(solve(A, B)).
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
   Dict = M.put([id: _Id, op: Op]).

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
   ;  resource_error(to(M.device, Device))
   ).

'@='(Left, Right) :-
   eval_(Right, Left).
eval_(A<B, C) =>
   eval_(A, A1),
   eval_(B, B1),
   push(A1<B1, C).
eval_(A>B, C) =>
   eval_(B<A, C).
eval_(A=<B, C) =>
   eval_(-(A>B) + 1, C).
eval_(A>=B, C) =>
   eval_(-(A<B) + 1, C).
eval_(A=\=B, C) =>
   eval_((A<B)+(A>B), C).
eval_(A=:=B, C) =>
   eval_(-(A=\=B)+1, C).
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
eval_(A @ B, C) =>
   eval_(A, A1),
   eval_(B, B1),
   Dim1 = A1.ndim(),
   Dim2 = B1.ndim0(),
   (  A1.ndim() > 1, B1.ndim() > 1
   -> nth1(Dim1, Shape1, 1, A1.shape()),
      nth1(Dim2, Shape2, 1, B1.shape())
   ;  Shape1 = A1.shape(),
      Shape2 = B1.shape()
   ),
   A3 = A1.reshape(Shape1),
   B2 = B1.reshape(Shape2), B3 = B2.swapaxes(B2.ndim0(), Dim2),
   eval_(A3 * B3, C1),
   C = C1.sum([C1.ndim0()]).
eval_(solve(A, B), X) =>
   eval_(A, A1),
   eval_(B, B1),
   push(solve(A1.contiguous(), B1.contiguous()), X).
eval_(A, R), is_dict(A, array) =>
   A = R.
eval_(A, R), number(A) =>
   R = array{}.full([], A).

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

M.ndim0() := NDim :-
   NDim #= M.ndim() - 1.

M.is_contiguous() := Res :-
   maplist(view:is_contiguous, M.views, [H | T]),
   foldl(mkconj, T, H, Res).

% Runtime
% =======

M.realize() := M :-
   % TODO: optimization
   create_schedule([M], Schedule),  % toposort of graph
   maplist(compile, Schedule, CompiledSchedule), % generate device specific code 
   allocate_schedule(Schedule),
   run_schedule(CompiledSchedule).

% Compilation
% ============
M.compile() := Dict :-
   Dict = M.compile(M.device, M.op),
   (  debugging(compile)
   -> debug(compile, "~p", Dict.kernel)
   ;  true
   ).
   % (  debugging(compile), Dict.kernel \== true
   % -> with_output_to(string(S), listing(Dict.kernel)),
   %    debug(compile, "~s", S)
   % ;  true
   % ).

:- multifile compile/4.
:- det(compile/4).

create_schedule(Arrays, Schedule) :-
   maplist(array_graph, Arrays, Graphs),
   foldl(ugraph_union, Graphs, [], Graph),
   top_sort(Graph, RSchedule),
   reverse(RSchedule, Schedule).

array_graph(Array, Graph) :-
   phrase(array_graph(Array), Edges),
   vertices_edges_to_ugraph([Array], Edges, Graph).

array_graph(Array), is_dict(Array, array) ==>
   (  {var(Array.data)}
   -> array_graph(Array, Array.op)
   ;  []
   ).
array_graph(Parent, Array), is_dict(Array, array) ==>
   array_graph(Array),
   [Parent-Array].
array_graph(Parent, Op) ==>
   (  {compound(Op)}
   -> {compound_name_arguments(Op, _, Args)},
      sequence(array_graph(Parent), Args)
   ;  []
   ).

% Allocation
% ==========
allocate_schedule(Schedule) :-
   maplist(allocate, Schedule).

allocate(M) :-
   (  var(M.data)
   -> compound_name_arity(M.data, data, M.datasize)
   ;  true
   ).

run_schedule(Schedule) :-
   maplist(run_scheduleitem, Schedule).

run_scheduleitem(M) :-
   run_scheduleitem(M.device, M).
run_scheduleitem(prolog, M) :-
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

M.index_input(Index) := AST-Value :-
   IndexExpr-ValidExpr = M.index_expr(Index),
   (  skip_view(M.op, constant(Constant))
   -> IndexAST = (Value = Constant)
   ;  IndexAST = (FlatIndex is IndexExpr+1, arg(FlatIndex, M.id, Value))
   ),
   (  ValidExpr = true
   -> (  IndexAST = (Value = Constant)
      -> Value = Constant, AST = true
      ;  AST = IndexAST
      )
   ;  AST = (  ValidExpr
            -> IndexAST
            ;  Value = 0
            )
   ).
skip_view(view(M), Op) =>
   skip_view(M.op, Op).
skip_view(Op, R) =>
   R = Op.

% DTypes
% ======
dtype(prolog, 0, R) => R = boolean.
dtype(prolog, 1, R) => R = boolean.
dtype(prolog, X, R), float(X) => R = float.
dtype(prolog, X, R), rational(X) => R = rational.
dtype(prolog, X, R), integer(X) => R = integer.
dtype(prolog, X, DType) => when(ground(X), dtype(prolog, X, DType)).

broadcast_dtype(prolog, boolean, integer).
broadcast_dtype(prolog, integer, rational).
broadcast_dtype(prolog, rational, float).

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

:- begin_tests(create_schedule).

test('one array, no dependencies') :-
    A = array{data: _, op: true},
    create_schedule([A], Schedule),
    Schedule == [A].

test('one array, one dependency') :-
    B = array{data: _, op: true},
    A = array{data: _, op: op1(B)},
    create_schedule([A], Schedule),
    Schedule == [B, A].

test('one array, chain of two dependencies') :-
    C = array{data: _, op: true},
    B = array{data: _, op: op1(C)},
    A = array{data: _, op: op2(B)},
    create_schedule([A], Schedule),
    Schedule == [C, B, A].

test('two independent arrays') :-
    A = array{data: _, op: true},
    B = array{data: _, op: true},
    create_schedule([A, B], Schedule),
    Schedule == [B, A].

test('C = A+B') :-
    A = array{data: _, op: true},
    B = array{data: _, op: true},
    C = array{data: _, op: A+B},
    create_schedule([C], Schedule),
    Schedule == [B, A, C].

:- end_tests(create_schedule).

:- begin_tests(array_tolist).

test('4x4') :-
    A = array{}.empty([4, 4]),
    List = A.tolist(),
    length(List, 4),
    maplist([L]>>length(L, 4), List).

:- end_tests(array_tolist).

:- begin_tests(array_matmul).

test('2d @ 1d') :-
  A = array{}.fromlist([[1,2],[3,4]]),
  B = array{}.fromlist([5,6]),
  C @= A @ B,
  C.tolist() == [17, 39].

test('2d @ 2d') :-
  A = array{}.arange(9).reshape([3, 3]),
  C @= A @ A,
  [[ 15,  18,  21],
   [ 42,  54,  66],
   [ 69,  90, 111]] = C.tolist().

:- end_tests(array_matmul).
