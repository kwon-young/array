:- module(array, [
   op(700, xfx, @=),
   op(400, yfx, @),
   '@='/2
]).

:- use_module(library(clpfd), except([transpose/2, sum/3])).
:- use_module(library(pairs)).
:- use_module(library(dcg/high_order)).

view:_.from_shape(Shape) := View :-
   shape_strides(Shape, Strides),
   shape_mask(Shape, Mask),
   View = view{shape: Shape, strides: Strides, mask: Mask, offset: 0}.
view:M.with_shape(Shape) := View :-
   View = M.put([shape: Shape, strides: _, mask: _]).
view:M.with_zip(Zip) := View :-
   same_length(Zip, Shape),
   View = M.with_shape(Shape),
   Zip = View.zip().

view:M.reshape(Shape) := Dict :-
   merge_dims(M.zip(), MergedPairs),
   Dict = M.with_shape(Shape),
   merge_dims(Dict.zip(), MergedPairs).

view:M.t() := Dict :-
   Dict = M.transpose().
view:M.transpose() := Dict :-
   same_length(M.shape, Shape),
   Dict = M.with_shape(Shape),
   reverse(M.zip(), Dict.zip()).
view:M.swapaxes(Axis1, Axis2) := Dict :-
   swap_nth0(Axis1, Axis2, M.zip(), Zip),
   Dict = M.with_zip(Zip).
view:M.permute(Axes) := Dict :-
   In = M.zip(),
   maplist({In}/[I, O]>>nth0(I, In, O), Axes, Out),
   Dict = M.with_zip(Out).
view:M.expand(Shape) := Dict :-
   Dict = M.broadcast(Shape).
view:M.squeeze() := Dict :-
   findall(Axis, nth0(Axis, M.shape, 1), Axes),
   Dict = M.squeeze(Axes).
view:M.squeeze(Axes) := Dict :-
   sort(0, @>, Axes, Axes_),
   foldl([Axis, In, Out]>>nth0(Axis, In, 1-_-_, Out), Axes_, M.zip(), Zip),
   Dict = M.with_zip(Zip).
view:M.pad(Padding) := Dict :-
   maplist(pad_dim, Padding, M.zip(), Zip, Offsets),
   clpfd:sum(Offsets, #=, PaddingOffset),
   Offset #= M.offset + PaddingOffset,
   Dict = M.with_zip(Zip).put(offset, Offset).
view:M.shrink(Shrink) := Dict :-
   foldl(shrink_dim, Shrink, M.zip(), Zip, M.offset, Offset),
   Dict = M.with_zip(Zip).put(offset, Offset).

shrink_dim(Start-End, Dim-Stride-_, Dim1-Stride-Mask, In, Out) :-
   mask(Dim, Start-End),
   Dim1 #= (End - Start),
   dim_mask(Dim1, Mask),
   Out #= In + Start*Stride.

pad_dim(Low-High, Dim1-Stride-(Min1-Max1), Dim2-Stride-(Min2-Max2), Offset) :-
   Dim2 #= Dim1 + Low + High,
   Min2 #= Min1 + Low,
   Max2 #= Max1 + Low,
   Offset #= -(Low*Stride).

view:M.zip() := Zip :-
   maplist([Dim, Stride, Mask, Dim-Stride-Mask]>>true, M.shape, M.strides, M.mask, Zip).
view:M.size() := Size :-
   shape_size(M.shape, Size).
view:M.ndim() := NDim :-
   length(M.shape, NDim).
view:M.is_contiguous() := Res :-
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
   Dict = array{id: _, views: Views, dtype:DType, device:Device, data: _, datasize: DataSize, op: true}.

push(view(Views), M, Dict) :-
   M1 = M.put(views, Views),
   (  M.op = view(_)
   -> Dict = M1
   ;  Dict = M1.push_op(view(M))
   ).
push(constant(Value, Options), M, Dict) :-
   merge_options(Options, [dtype(_)], Merged),
   M1 = M.empty([], Merged),
   dtype(M1.device, Value, M1.dtype), % TODO: broadcast dtype
   Dict = M1.push_op(constant(Value)).
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
push(elementwise(Op, Args), C) :-
   (  dicts_same_value_for_key(Args, device, _)
   -> true
   ;  domain_error(device, Args)
   ),
   (  dicts_same_value_for_key(Args, dtype, _)
   -> true
   ;  domain_error(dtype, Args)
   ),
   broadcast(Args, [H | T]),
   Term =.. [Op, H | T],
   C = H.empty(H.shape()).push_op(Term).

dicts_same_value_for_key(List, Key, Value) :-
   maplist({Value, Key}/[Dict]>>get_dict(Key, Dict, Value), List).

M.push_op(Op) := Dict :-
   Dict = M.put([id: _Id, op: Op]).

M.push_view(View) := Dict :-
   Dict = M.push(view([View | M.views])).
M.pop_view(View) := Dict :-
   M.views = [View | Views],
   Dict = M.push(view(Views)).
M.replace_view(Old, New) := Dict :-
   Dict = M.pop_view(Old).push_view(New).
M.replace_view(View) := Dict :-
   Dict = M.replace_view(_, View).
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
   Dict = M.default([shape(Shape) | Options]).
M.fromlist(List) := Dict :-
   Dict = M.fromlist(List, []).
M.fromlist(List, Options) := Dict :-
   list_shape(List, Shape),
   flatten(List, Flat),
   M1 = M.empty(Shape, Options),
   Device = M1.device,
   DType = M1.dtype,
   debug(fromlist, "DType ~p", [DType]),
   maplist({Device, DType}/[X]>>dtype(Device, X, DType), Flat), % TODO: type broadcasting
   compound_name_arguments(M1.data, data, Flat),
   Dict = M1.

dtype(prolog, X, float), integer(X) => true.
dtype(prolog, X, R), float(X) => R = float.
dtype(prolog, X, R), integer(X) => R = integer.
dtype(prolog, true, R) => R = boolean.
dtype(prolog, false, R) => R = boolean.
dtype(prolog, X, DType) => when(ground(X), dtype(prolog, X, DType)).

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
   Offset @= array{}.full([], Start, Options) - array{}.full([], Step, Options),
   Dict @= M1.cumalu(0, +) + Offset.

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
M.shrink(Shrink) := Dict :-
   Dict = M.replace_view(M.view().shrink(Shrink)).
M.pad(Padding) := Dict :-
   Dict = M.pad(Padding, []).
M.pad(Padding, Options) := Dict :-
   M1 = M.replace_view(M.view().pad(Padding)),
   (  option(constant(Value), Options)
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
   maplist([I, K, D, E]>>(E #= I - D*(K-1)), LastDims, Kernel, Dilations, Effective),
   debug(pool, "Effective ~p", [Effective]),
   maplist([E, S, O]>>(O #= (E - 1) // S + 1), Effective, Strides, Output),
   debug(pool, "Output ~p", [Output]),
   maplist([S, O, SO]>>(SO #= O*S), Strides, Output, StridesOutput),
   debug(pool, "StridesOutput ~p", [StridesOutput]),
   maplist([E, SO, F]>>((SO #> E) #<==> B, F #= 1 + B), Effective, StridesOutput, Fs),
   debug(pool, "Fs ~p", [Fs]),
   maplist([I, D, F, U]>>(U #= I*F+D), LastDims, Dilations, Fs, Unfolded),
   debug(pool, "Unfolded ~p", [Unfolded]),
   maplist([U, K, T]>>(T #= K*U), Unfolded, Kernel, Target),
   debug(pool, "Target ~p", [Target]),
   maplist([I, T, R]>>ceildiv(T, I, R), LastDims, Target, Repeat),
   lpad(M.ndim(), 1, Repeat, PaddedRepeat),
   debug(pool, "Repeat ~p", [PaddedRepeat]),
   M1 = M.repeat(PaddedRepeat),
   debug(pool, "Repeated ~p", [M1.shape()]),
   append(PrefixDims, Target, PrefixedTarget),
   lpad(M1.ndim(), 0, [], Zeros),
   pairs_keys_values(Shrink1, Zeros, PrefixedTarget),
   debug(pool, "Shrink1 ~p", [Shrink1]),
   M2 = M1.shrink(Shrink1),
   debug(pool, "Shrinked1 ~p", [M2.shape()]),
   clpfd:transpose([Kernel, Unfolded], KU),
   flatten(KU, Reshape1_),
   append(PrefixDims, Reshape1_, Reshape1),
   debug(pool, "Reshape1 ~p", [Reshape1]),
   M3 = M2.reshape(Reshape1),
   clpfd:transpose([Kernel, StridesOutput], KSO),
   flatten(KSO, Shrink2__),
   append(PrefixDims, Shrink2__, Shrink2_),
   lpad(M3.ndim(), 0, [], Zeros2),
   pairs_keys_values(Shrink2, Zeros2, Shrink2_),
   debug(pool, "Shrink2 ~p", [Shrink2]),
   M4 = M3.shrink(Shrink2),
   debug(pool, "Shrinked2 ~p", [M4.shape()]),
   clpfd:transpose([Kernel, Output, Strides], KOS),
   flatten(KOS, Reshape2_),
   append(PrefixDims, Reshape2_, Reshape2),
   debug(pool, "Reshape2 ~p", [Reshape2]),
   M5 = M4.reshape(Reshape2),
   lpad(N, 1, [], Ones),
   clpfd:transpose([Kernel, Output, Ones], KO1),
   flatten(KO1, Shrink3__),
   append(PrefixDims, Shrink3__, Shrink3_),
   lpad(M5.ndim(), 0, [], Zeros3),
   pairs_keys_values(Shrink3, Zeros3, Shrink3_),
   debug(pool, "Shrink3 ~p", [Shrink3]),
   M6 = M5.shrink(Shrink3),
   debug(pool, "Shrinked3 ~p", [M6.shape()]),
   clpfd:transpose([Kernel, Output], KO),
   flatten(KO, Reshape3_),
   append(PrefixDims, Reshape3_, Reshape3),
   debug(pool, "Reshape3 ~p", [Reshape3]),
   M7 = M6.reshape(Reshape3),
   N1 is M7.ndim() - 1,
   numlist(0, N1, Axes),
   same_length(PrefixDims, PrefixAxes),
   append(PrefixAxes, PoolAxes, Axes),
   once(foldl([A, B, [A, B | R], R]>>true, KernelAxes, DimAxes, PoolAxes, [])),
   append([PrefixAxes, DimAxes, KernelAxes], PermuteAxes),
   debug(pool, "Permute ~p", [PermuteAxes]),
   M8 = M7.permute(PermuteAxes),
   debug(pool, "Permuted ~p", [M8.shape()]),
   Dict = M8.

ceildiv(A, B, C) :-
   C #= (A+B-1)//B.

M.reduce(Axes, Op, KeepDim) := Dict :-
   must_be(list, Axes),
   must_be(oneof([+, <]), Op),
   M1 = M.push(reduce(Op, Axes)),
   (  KeepDim
   -> M1 = Dict
   ;  Dict = M1.squeeze(Axes)
   ).
M.sum() := Dict :-
   High is M.ndim() - 1,
   numlist(0, High, Axes),
   Dict = M.sum(Axes).
M.sum(Axes) := Dict :-
   Dict = M.sum(Axes, false).
M.sum(Axes, KeepDim) := Dict :-
   Dict = M.reduce(Axes, +, KeepDim).
M.max() := Dict :-
   High is M.ndim() - 1,
   numlist(0, High, Axes),
   Dict = M.max(Axes).
M.max(Axes) := Dict :-
   Dict = M.max(Axes, false).
M.max(Axes, KeepDim) := Dict :-
   Dict = M.reduce(Axes, <, KeepDim).
M.cumalu(Axis, Op) := Dict :-
   N1 #= M.ndim() - 1,
   M1 = M.swapaxes(N1, Axis),
   debug(cumalu, "Swapped1 ~p", [M1.shape()]),
   length(Padding, M1.ndim()),
   last(M1.shape(), Dim),
   Dim1 #= Dim - 1,
   once(append(ZeroPadding, [Dim1-0], Padding)),
   maplist(=(0-0), ZeroPadding),
   M2 = M1.pad(Padding),
   debug(cumalu, "Padded ~p", [M2.shape()]),
   M3 = M2.pool([Dim]),
   debug(cumalu, "Pooled ~p", [M3.shape()]),
   N2 #= M3.ndim() - 1,
   M4 = M3.reduce([N2], Op, false),
   debug(cumalu, "reduced ~p", [M4.shape()]),
   M5 = M4.swapaxes(Axis, N1),
   debug(cumalu, "Swapped2 ~p", [M5.shape()]),
   Dict = M5.


M.contiguous() := Dict :-
   (  M.is_contiguous()
   -> Dict = M
   ;  Dict = M.push(contiguous)
   ).
M.is_contiguous() := Res :-
   maplist(view:is_contiguous, M.views, [H | T]),
   foldl(mkconj, T, H, Res).

M.to(Device) := Dict :-
   (  M.device = Device
   -> Dict = M
   ;  resource_error(to(M.device, Device))
   ).

M.realize() := M :-
   % TODO: optimization
   create_schedule([M], Schedule),  % toposort of graph
   maplist(compile, Schedule, CompiledSchedule), % generate device specific code 
   allocate_schedule(Schedule),
   run_schedule(CompiledSchedule).

M.compile() := Dict :-
   Dict = M.compile(M.device, M.op),
   (  debugging(compile), Dict.kernel \== true
   -> with_output_to(string(S), listing(Dict.kernel)),
      debug(compile, "~s", S)
   ;  true
   ).

M.compile(prolog, true) := Dict :-
   Dict = M.put(kernel, true).
M.compile(prolog, view(_)) := Dict :-
   Dict = M.put(kernel, true).
M.compile(prolog, constant(_)) := Dict :-
   Dict = M.put(kernel, true).
M.compile(prolog, contiguous(Parent)) := Dict :-
   variant_sha1(M, KernelId), % TODO: restrict to correct dependencies
   length(Index, M.ndim()),
   Head =.. [KernelId, M.id, Parent.id | Index],
   ModuleHead = kernel:Head,
   ParentAST-ParentValue = Parent.index_input(Index),
   MIndexExpr-MValidExpr = M.index_expr(Index),
   mkconj(
      ParentAST, 
      (  MValidExpr
      -> MIndex is MIndexExpr+1,
         nb_setarg(MIndex, M.id, ParentValue)
      ;  true
      ),
      Body),
   Kernel = (ModuleHead :- Body),
   retractall(ModuleHead),
   asserta(Kernel),
   CallHead =.. [KernelId, M.data, Parent.data | Index],
   Dict = M.put([kernel=(kernel:CallHead), index=Index]).
M.compile(prolog, A<B) := Dict :-
   Dict = M.compile(prolog, elementwise(<, [A, B])).
M.compile(prolog, A+B) := Dict :-
   Dict = M.compile(prolog, elementwise(+, [A, B])).
M.compile(prolog, A*B) := Dict :-
   Dict = M.compile(prolog, elementwise(*, [A, B])).
M.compile(prolog, elementwise(Op, Args)) := Dict :-
   variant_sha1(M, KernelId),
   length(Index, M.ndim()),
   maplist(get_dict(id), Args, Ids),
   append(Ids, Index, IdsIndex),
   Head =.. [KernelId, M.id | IdsIndex],
   ModuleHead = kernel:Head,
   maplist(index_input(Index), Args, Pairs),
   pairs_keys_values(Pairs, ArgsAsts, ArgsValue),
   MIndexExpr-MValidExpr = M.index_expr(Index),
   foldl(mkconj, ArgsAsts, true, ArgsAst),
   Expr =.. [Op | ArgsValue],
   (  Op = (<)
   -> MExpr = (Expr -> MValue = 1 ; MValue = 0)
   ;  MExpr = (MValue is Expr)
   ),
   mkconj(ArgsAst, MExpr, Body),
   Kernel = (ModuleHead :-
      Body,
      (  MValidExpr
      -> MIndex is MIndexExpr+1,
         nb_setarg(MIndex, M.id, MValue)
      ;  true
      )
   ),
   retractall(ModuleHead),
   asserta(Kernel),
   maplist(get_dict(data), Args, Datas),
   append(Datas, Index, DatasIndex),
   CallHead =.. [KernelId, M.data | DatasIndex],
   Dict = M.put([kernel=(kernel:CallHead), index=Index]).
M.compile(prolog, reduce(Op, Axes, Parent)) := Dict :-
   variant_sha1(M, KernelId),
   length(Index, M.ndim()),
   Head =.. [KernelId, M.id, Parent.id | Index],
   ModuleHead = kernel:Head,
   same_length(Axes, AccIndex),
   foldl(replace_nth0, AccIndex, Axes, Index, FullIndex),
   ParentAST-ParentValue = Parent.index_input(FullIndex),
   MIndexExpr-MValidExpr = M.index_expr(Index),
   AccExpr =.. [Op, AccValue, ParentValue],
   (  Op = (<)
   -> Identity is -inf,
      NewAccExpr = (
      (  AccExpr
      -> NewAccValue = ParentValue
      ;  NewAccValue = AccValue
      ))
   ;  Identity is 0,
      NewAccExpr = (NewAccValue is AccExpr)
   ),
   mkconj(ParentAST, (
      arg(1, Acc, AccValue),
      NewAccExpr,
      nb_setarg(1, Acc, NewAccValue)),
      AccAST),
   ParentShape = Parent.shape(),
   maplist({ParentShape}/[Axis, I, between(0, Dim1, I)]>>(
           nth0(Axis, ParentShape, Dim), Dim1 is Dim-1), 
           Axes, AccIndex, BList),
   comma_list(Betweens, BList),
   Kernel = (ModuleHead :-
      Acc = acc(Identity, _),
      forall(Betweens, AccAST),
      arg(1, Acc, MValue),
      (  MValidExpr
      -> MIndex is MIndexExpr+1,
         nb_setarg(MIndex, M.id, MValue)
      ;  true
      )
   ),
   retractall(ModuleHead),
   asserta(Kernel),
   CallHead =.. [KernelId, M.data, Parent.data | Index],
   Dict = M.put([kernel=(kernel:CallHead), index=Index]).

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

'@='(Left, Right) :-
   eval_(Right, Left).
eval_(A<B, C) =>
   eval_(A, A1),
   eval_(B, B1),
   push(A1<B1, C).
eval_(A+B, C) =>
   eval_(A, A1),
   eval_(B, B1),
   push(A1+B1, C).
eval_(A-B, C) =>
   Minus = B.full([], -1, [dtype(B.dtype)]),
   eval_(A + (Minus*B), C).
eval_(A*B, C) =>
   eval_(A, A1),
   eval_(B, B1),
   push(A1*B1, C).
eval_(A @ B, C) =>
   eval_(A, A1),
   eval_(B, B1),
   Dim1 = A1.ndim(),
   Dim2 #= max(B1.ndim() - 1, 1),
   (  A1.ndim() > 1, B1.ndim() > 1
   -> nth1(Dim1, Shape1, 1, A1.shape()),
      nth1(Dim2, Shape2, 1, B1.shape())
   ;  Shape1 = A.shape,
      Shape2 = B.shape
   ),
   A3 = A1.reshape(Shape1).swapaxes(Dim1, Dim2),
   B3 = B1.reshape(Shape2).swapaxes(B1.ndim(), Dim2).swapaxes(Dim1, Dim2),
   eval_(A3 * B3, C1),
   Axis1 #= C1.ndim() - 2,
   C = C1.sum([Axis1]).
eval_(A, R), is_dict(A, array) =>
   A = R.
eval_(A, R), number(A) =>
   R = array{}.full([], A).

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
   (  M.kernel = true
   -> true
   ;  maplist([Dim, I, between(0, Dim1, I)]>>(Dim1 is Dim-1), M.shape(), M.index, L),
      (  L = []
      -> Betweens = true
      ;  comma_list(Betweens, L)
      ),
      forall(Betweens, M.kernel)
   ).

replace_nth0(New, N, In, Out) :-
   replace_nth0(_, New, N, In, Out).
replace_nth0(Old, New, N, In, Out) :-
   nth0(N, In, Old, Tmp),
   nth0(N, Out, New, Tmp).

swap_nth0(N1, N2, In, Out) :-
   replace_nth0(V1, V2, N1, In, Tmp),
   replace_nth0(V2, V1, N2, Tmp, Out).

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
list_shape(L, Shape) :-
   list_shape_(Shape, L).
list_shape_(Shape, L), is_list(L) =>
   length(L, Dim),
   Shape = [Dim | Dims],
   maplist(list_shape_(Dims), L).
list_shape_(Shape, _) => Shape = [].


broadcast(In, Out) :-
   maplist(view, In, InViews),
   broadcast_views(InViews, OutViews),
   maplist(replace_view, OutViews, In, Out).

:- table broadcast_views/2.

broadcast_views(In, Out) :-
   foldl(broadcast_shape, In, [], Shape),
   maplist(view:broadcast(Shape), In, Out).

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

:- table view:broadcast/3.

view:In.broadcast(Shape) := Out :-
   length(Shape, N),
   lpad(N, 1-0-(0-1), In.zip(), Zip),
   Out = In.with_shape(Shape),
   maplist(view:broadcast_, Shape, Zip, Out.zip()).

view:broadcast_(1, Pair, Pair) :-
   Pair = Dim-_-_,
   Dim #\= 1.
view:broadcast_(Dim, 1-_-(0-Max), Dim-0-(0-NewMax)) :-
   Dim #\= 1,
   NewMax #= Max * Dim. % Max is either 0 or 1
view:broadcast_(Dim, Dim-Stride-Mask, Dim-Stride-Mask).

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
