:- module(array, []).

:- use_module(library(clpfd)).
:- use_module(library(pairs)).
:- use_module(library(dcg/high_order)).

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
view:M.ndim() := NDim :-
   length(M.shape, NDim).
view:M.contiguous() := Res :-
   (  shape_strides(M.shape, M.strides),
      shape_mask(M.shape, M.mask),
      M.offset = 0
   -> Res = true
   ;  Res = false
   ).

view:View.index_expr(Index) := FlatIndex :-
   foldl([I, Stride, Sum, Sum+I*Stride]>>true,
         Index, View.strides, View.offset, FlatIndex).
view:View.reverse_index_expr(FlatIndex) := Index :-
   shape_strides(View.shape, Strides),
   foldl([Stride, Flat // Stride, Flat, Flat mod Stride]>>true,
         Strides, Index, FlatIndex, _).
view:View.valid_expr(Index) := ValidExpr :-
   maplist([I, Min-Max, (I >= Min, I < Max)]>>true,
           Index, View.mask, ValidExpr).


M.default() := Dict :-
   Dict = M.default([]).
M.default(Options) := Dict :-
   dict_options(M, MOptions),
   merge_options(Options, MOptions, Merged),
   option(dtype(DType), Merged, float),
   option(device(Device), Merged, prolog),
   Dict = array{views: [], dtype:DType, device:Device, data: _, op: true}.

M.push(contiguous) := Dict :-
   Dict = M.empty().push_view(view{}.from(M.shape())).push_op(contiguous(M)).

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
M.ndim() := NDim :-
   NDim = M.view().ndim().

M.empty(Shape) := Dict :-
   Dict = M.empty(Shape, []).
M.empty(Shape, Options) := Dict :-
   shape_size(Shape, Size),
   Dict = M.default(Options).push_view(view{}.from_shape([Size])).reshape(Shape).

M.tolist() := List :-
   shape_list(M.shape(), List),
   flatten(List, Flat),
   compound_name_arguments(M.contiguous().to(prolog).realize().data, data, Flat).

M.reshape(Shape) := Dict :-
   (  shape_size(Shape, M.size())
   -> (  View = M.view().reshape(Shape)
      -> Dict = M.replace_view(View)
      ;  Dict = M.push_view(view{}.from_shape(Shape))
      )
   ;  domain_error(M.shape(), Shape)
   ).

M.contiguous() := Dict :-
   Dict = M.push(contiguous).

M.to(Device) := Dict :-
   (  M.device = Device
   -> Dict = M
   ;  resource_error(to(M.device, Device))
   ).

M.realize() := M :-
   create_schedule([M.push(sink)], Schedule),  % toposort of graph
   maplist(compile, Schedule, CompiledSchedule),
   run_schedule(CompiledSchedule).  % generate device specific code and execute

create_schedule(Arrays, Schedule) :-
   maplist(array_graph, Arrays, Graphs),
   foldl(ugraph_union, Graphs, [], Graph),
   top_sort(Graph, Schedule).

array_graph(Array, Graph) :-
   phrase(array_graph(Array), Edges),
   vertices_edges_to_ugraph([], Edges, Graph).

array_graph(Array), is_dict(Array, array) ==>
   (  {var(Array.data)}
   -> array_graph(Array.op, Array)
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

compile(In, Out) :-
   compile(In.device, In.op, In, Out).

M.compile(prolog, true) := Dict :-
   Dict = M.put(kernel, true).
M.compile(prolog, contiguous(Parent)) := Dict :-
   (  M.contiguous() = true
   -> true
   ;  domain_error(contiguous, M)
   ),
   variant_sha1(M.put(op, contiguous(Parent.data)), KernelId),
   length(Index, M.ndim()),
   Head =.. [KernelId, M.id, Parent.id, Index],
   ModuleHead = kernel:Head,
   ParentIndexExpr-ParentValidExpr = Parent.index_expr(Index),
   MIndexExpr-_ = M.index_expr(Index),
   Kernel = (ModuleHead :-
      (  ParentValidExpr
      -> ParentIndex is ParentIndexExpr,
         arg(ParentIndex, Parent.id, ParentValue)
      ;  ParentValue = 0
      ),
      MIndex is MIndexExpr,
      nb_setarg(MIndex, M.id, ParentValue)
   ),
   retractall(ModuleHead),
   asserta(Kernel),
   CallHead =.. [KernelId, Parent.data, M.data, Index],
   Dict = M.put([kernel=(kernel:CallHead), index=Index]).

M.index_expr(Index) := IndexExpr-ValidExpr :-
   M.views = [View | Views],
   foldl([V, Valid, FlatIn, FlatOut]>>(
            view:reverse_index_expr(FlatIn, V, Index_),
            view:valid_expr(Index_, V, Valid),
            view:index_expr(Index_, V, FlatOut)
         ), Views, Valids, View.index_expr(Index), IndexExpr),
   comma_list(Valids, ValidExpr).

run_schedule(Schedule) :-
   maplist(run_scheduleitem, Schedule).

run_scheduleitem(M) :-
   run_scheduleitem(M.device, M).
run_scheduleitem(prolog, M) :-
   Size1 is M.size() - 1,
   compound_name_arity(M.data, data, M.size()),
   (  M.kernel = true
   -> true
   ;  forall(between(0, Size1, M.index), M.kernel)
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

% :- det(merge_dims/2).
:- table merge_dims/2.

merge_dims([], [1-1-(0-1)]).
merge_dims([H | T], MergedPairs) :-
   merge_dims(T, H, MergedPairs).

merge_dims([], Acc, [Acc]).
merge_dims([Dim-Stride-(Min-Max) | T], AccDim-AccStride-(AccMin-AccMax), Merged) :-
   (  full_mask(Dim, Min-Max), full_mask(AccDim, AccMin-AccMax)
   ;  single_element_mask(Dim, Min-Max), single_element_mask(AccDim, AccMin-AccMax)
   ),
   AccStride #= Dim * Stride,
   NewAccDim #= AccDim * Dim,
   NewMin #= AccMin*AccDim + Min,
   NewMax #= (AccMax-1)*Dim + Max,
   merge_dims(T, NewAccDim-Stride-(NewMin-NewMax), Merged).
merge_dims([H | T], Acc, [Acc | MergedTail]) :-
   H = Dim-Stride-_,
   Acc = _-AccStride-_,
   AccStride #\= Dim * Stride,
   merge_dims(T, H, MergedTail).

mask(Dim, Min-Max) :-
   Min #>= 0,
   Max #>= 0,
   Min #=< Dim,
   Max #=< Dim,
   Max #>= Min.
full_mask(Dim, 0-Dim).
single_element_mask(Dim, Min-Max) :-
   mask(Dim, Min-Max),
   Max - Min #= 1.

shape_list([], _).
shape_list([Dim | Shape], L) :-
   length(L, Dim),
   maplist(shape_list(Shape), L).

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

:- begin_tests(index_expr).

test('contiguous') :-
    A = array{}.empty([4, 5]),
    IndexExpr-ValidExpr = A.index_expr([1, 2]),
    7 is IndexExpr,
    ValidExpr == true.

test('offset') :-
    V = view{}.from_shape([4, 5]).put(offset, 10),
    A = array{}.default().push_view(V),
    IndexExpr-ValidExpr = A.index_expr([1, 2]),
    17 is IndexExpr,
    ValidExpr == true.

test('sliced') :-
    % A 3x4 slice from a 10x10 array, starting at (2,3)
    V = view{shape:[3,4], strides:[10,1], mask:[0-3,0-4], offset:23},
    A = array{}.default().push_view(V),
    % logical coordinate (1,1) in the 3x4 slice
    % physical flat index should be for (2+1, 3+1) = (3,4) in 10x10 array
    % which is 3*10 + 4 = 34
    IndexExpr-ValidExpr = A.index_expr([1, 1]),
    34 is IndexExpr,
    ValidExpr == true.

test('transposed') :-
    % A 10x20 array, transposed to 20x10
    V = view{shape:[20,10], strides:[1,20], mask:[0-20,0-10], offset:0},
    A = array{}.default().push_view(V),
    % logical coordinate (2,1) in 20x10 array
    % this corresponds to (1,2) in 10x20 array
    % physical flat index is 1*20 + 2 = 22
    IndexExpr-ValidExpr = A.index_expr([2, 1]),
    22 is IndexExpr,
    ValidExpr == true.

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
  A.op == buffer(6),
  length(A.views, 1),
  A.view().shape == [2,3].

:- end_tests(array_empty).
