:- module(array, [
   op(700, xfx, @=),
   op(400, yfx, @),
   '@='/2
]).

:- use_module(library(lists), except([flatten/2])).
:- use_module(library(clpfd), except([transpose/2, sum/3])).
:- use_module(library(pairs)).
:- use_module(library(dcg/high_order)).
:- use_module(library(clpBNR)).
:- use_module(library(rbtrees)).
:- use_module(view).
:- use_module(dtype).
:- use_module(minimalloc).
% :- use_module(optim).
:- use_module(library(egraph)).

:- multifile compile/4.
:- multifile allocate/2.
% :- multifile dtype/3.
% :- multifile broadcast_dtype/3.
:- multifile to/4.
:- multifile dtype_size/3.
:- multifile default_format/3.
:- multifile float_formats/2.

:- use_module(runtime_prolog).
:- use_module(runtime_c).
% after the runtimes: the lup tests need to run before clpBNR first sets its
% arithmetic flags
:- use_module(precision).

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
   compound_name_arguments(M1.to(prolog).realize().data, data, Flat).
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
   foldl(replace_nth0(1), Axes, M.shape(), Shape),
   sort(Axes, Axes_),
   (  Op == (<)
   -> Range::boolean,
      DType = boolean
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
   ;  Dict = M.to(M.device, Device)
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
   % TODO: optimization
   % once(phrase((
   %    add_term(M, Id),
   %    saturate([optim:operator_fusion]),
   %    extract(Id, M1)
   % ), [], _)),
   M1 = M,
   create_schedule([M1], Tolerance, Schedule),  % toposort of graph
   maplist(compile, Schedule, CompiledSchedule), % generate device specific code 
   allocate_schedule(Schedule),
   run_schedule(CompiledSchedule).

% Compilation
% ============
M.compile() := Dict :-
   once(Dict = M.compile(M.device, M.op)).
   % format("~p~n", [Dict.kernel]).

create_schedule(Arrays, NewSchedule) :-
   create_schedule(Arrays, inf, NewSchedule).
create_schedule(Arrays, Tolerance, NewSchedule) :-
   graph_schedule(Arrays, Schedule),
   % pool offsets need each array's dtype size
   choose_formats(Schedule, Arrays, Tolerance),
   allocation_scheme(Arrays, Schedule, NewSchedule).

graph_schedule(Arrays, Schedule) :-
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
