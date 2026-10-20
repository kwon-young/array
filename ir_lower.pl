:- module(ir_lower, [lower_kernel/5]).

/** <module> Lowering fused kernels to the kernel IR

lower_kernel/5 turns a fused schedule node into a kernel clause of the IR
(docs/kernel_ir.md), whose semantics every device shares:

  * each load is converted to the kernel's compute format, as C converts it
    when it loads an input into a variable of that type;
  * an operation is an expression over operands in the compute format: a
    variable only names a value a goal produces, a load, a cast, a
    comparison's result or a reduction;
  * an inlined node, fused(Node, Expr), is rounded to Node's format;
  * the result is converted to the output's format before it is stored.
*/

:- use_module(library(apply)).
:- use_module(library(assoc)).
:- use_module(library(dcg/high_order)).
:- use_module(array, []).
:- use_module(fusion, [inlined_nodes//1, node_index/3, read_shape/2]).
:- use_module(kernel_c, [compute_dtype/2]).
:- use_module(view, [replace_nth0/4]).

% lower_kernel(+Device, +M, +Op, -Kernel, -Arrays)
% Kernel is the IR clause computing Op into M on Device. Arrays are the
% arrays whose buffers are the head's, in order: M, then its inputs.
lower_kernel(Device, M, Op, Kernel, Arrays) :-
   top_expr(Op, M, Expr),
   phrase(array:op_args(Expr), AllArgs),
   list_to_ord_set(AllArgs, Args),
   Arrays = [M | Args],
   maplist(buffer, Arrays, Buffers),
   pairs_keys_values(BufferPairs, Arrays, Buffers),
   list_to_assoc(BufferPairs, BufferAssoc),
   load_formats(Device, M, Expr, Args, Compute, LoadFormats),
   pairs_keys_values(LoadPairs, Args, LoadFormats),
   list_to_assoc(LoadPairs, LoadAssoc),
   length(Index, M.ndim()),
   maplist(binder, Index, M.shape(), Domain0),
   conjunction(Domain0, Domain),
   Ctx = ctx{index: Index, node: M, buffers: BufferAssoc, loads: LoadAssoc,
             compute: Compute},
   phrase(value(Expr, Ctx, Value, Format), Goals0),
   Out = M.dtype(),
   phrase(cast(Out, Value, Format, Stored), Goals1),
   IndexExpr-Valid = M.index_expr(Index),
   [Buffer | _] = Buffers,
   append([Goals0, Goals1, [store(Buffer, IndexExpr, Stored)]], Goals),
   conjunction(Goals, Element0),
   guard(Valid, Element0, Element),
   Head =.. [kernel | Buffers],
   Kernel = (Head :- forall(Domain, Element)).

% The ops that compile to a cast or to random numbers at the top of a kernel.
top_expr(rand, _, Expr) =>
   Expr = rand.
top_expr(float(A), M, Expr) =>
   Expr = cast(A, M.dtype()).
top_expr(integer(A), M, Expr) =>
   Expr = cast(A, M.dtype()).
top_expr(Op, _, Expr) =>
   Expr = Op.

buffer(A, _-Format) :-
   Format = A.dtype().

conjunction(Goals, Conjunction) :-
   foldl(conjoin, Goals, true, Conjunction).

conjoin(Goal, Conjunction0, Conjunction) :-
   mkconj(Conjunction0, Goal, Conjunction).

% binder(?I, +Dim, -Binder): I ranges over a dimension of size Dim.
binder(I, Dim, between(0, Max, I)) :-
   Max is Dim - 1.

dimension(Shape, Axis, Dim) :-
   nth0(Axis, Shape, Dim).

guard(true, Goal0, Goal) =>
   Goal = Goal0.
guard(Valid, Goal0, Goal) =>
   Goal = (Valid -> Goal0 ; true).

% Formats
% =======

% load_formats(+Device, +M, +Expr, +Args, -Compute, -Formats)
% Formats are the formats Args are loaded in, and Compute the format
% operations compute in.
% A cast must see its input unchanged, so it keeps the input's own format.
load_formats(_, _, cast(A, _), Args, Compute, Formats), is_dict(A, array) =>
   maplist(array:dtype, Args, Formats),
   Compute = none.
load_formats(Device, _, A<B, Args, Compute, Formats) =>
   phrase(inlined_nodes(A<B), Inlined),
   append(Inlined, Args, Arrays),
   compute_format(Device, Arrays, Compute),
   same_length(Args, Formats),
   maplist(=(Compute), Formats).
load_formats(Device, M, Op, Args, Compute, Formats) =>
   phrase(inlined_nodes(Op), Inlined),
   append([M | Inlined], Args, Arrays),
   compute_format(Device, Arrays, Compute),
   same_length(Args, Formats),
   maplist(=(Compute), Formats).

% The C family computes in the smallest format holding every array; the
% Prolog device computes exactly, in its kind's format.
compute_format(prolog, Arrays, Format) =>
   maplist(get_dict(dtype), Arrays, Kinds),
   foldl(array:broadcast_dtype, Kinds, boolean, Kind),
   prolog_format(Kind, Format).
compute_format(_, Arrays, Format) =>
   compute_dtype(Arrays, Format).

prolog_format(float, Format) => Format = float64.
prolog_format(Kind, Format) => Format = Kind.

% cast(+Format, +In, +InFormat, -Out)//
cast(Format, In, InFormat, Out), InFormat == Format ==>
   { Out = In }.
cast(Format, In, _, Out) ==>
   [cast(Format, In, Out)].

% Values
% ======

% value(+Expr, +Ctx, -Value, -Format)//
% The goals computing Value, the value of Expr at the index of Ctx, in
% Format. Value is a value expression.
value(A, Ctx, Value, Format), is_dict(A, array) ==>
   load(A, Ctx, Value, Format).
% An inlined node is rounded to its format, as its buffer would be.
value(fused(Node, Expr), Ctx, Value, Format) ==>
   value(Expr, Ctx.put(node, Node), Value0, Format0),
   { Format = Node.dtype() },
   cast(Format, Value0, Format0, Value).
% Expr is computed at the index of the node that Via reads.
value(reindex(Via, Expr), Ctx, Value, Format) ==>
   { node_index(Via, Ctx.index, Index) },
   value(Expr, Ctx.put(index, Index), Value, Format).
value(reduce(Op, Axes, Parent), Ctx, Value, Format) ==>
   reduction(Op, Axes, Parent, Ctx, Value, Format).
value(contiguous(A), Ctx, Value, Format) ==>
   value(A, Ctx, Value, Format).
% The rounding is the cast of the enclosing fused/2.
value(float(A), Ctx, Value, Format) ==>
   value(A, Ctx, Value, Format).
value(integer(A), Ctx, Value, Format) ==>
   value(A, Ctx, Value, Format).
value(cast(A, To), Ctx, Value, Format) ==>
   value(A, Ctx, Value0, Format0),
   cast(To, Value0, Format0, Value),
   { Format = To }.
value(rand, _, Value, Format) ==>
   { Value = random_float },
   { Format = float64 }.
value(A < B, Ctx, Value, Format) ==>
   operands([A, B], Ctx, [VA, VB]),
   [(VA < VB -> Value = 1 ; Value = 0)],
   { Format = bool }.
value(Op, Ctx, Value, Format), compound(Op) ==>
   { compound_name_arguments(Op, Name, Args) },
   operands(Args, Ctx, Values),
   { compound_name_arguments(Value, Name, Values) },
   { Format = Ctx.compute }.

% The operands of an operation, in the compute format.
operands([], _, Values) ==>
   { Values = [] }.
operands([A | As], Ctx, Values) ==>
   value(A, Ctx, V0, F0),
   cast(Ctx.compute, V0, F0, V),
   operands(As, Ctx, Vs),
   { Values = [V | Vs] }.

% A load reads the element at the index of Ctx, or 0 outside a mask, and
% converts it to the load format.
load(A, Ctx, Value, Format) -->
   {  get_assoc(A, Ctx.buffers, Buffer),
      get_assoc(A, Ctx.loads, Format),
      IndexExpr-Valid = A.index_expr(Ctx.index),
      Buffer = _-BufferFormat
   },
   (  { array:skip_view(A.op, constant(Constant)) }
   -> guarded_value(Valid, cast(Format, Constant, Value), Value)
   ;  guarded_value(Valid, load(Buffer, IndexExpr, Value0), Value0),
      cast(Format, Value0, BufferFormat, Value)
   ).

guarded_value(true, Goal, _) ==>
   [Goal].
guarded_value(Valid, Goal, Value) ==>
   [(Valid -> Goal ; Value = 0)].

% A reduction of Ctx's node accumulates, in the node's format, the values of
% Parent at each index that the reduced axes add to the node's index.
reduction(Op, Axes, Parent, Ctx, Value, Format) -->
   {  Format = Ctx.node.dtype(),
      read_shape(Parent, Shape),
      maplist(dimension(Shape), Axes, Dims),
      same_length(Axes, Js),
      foldl(replace_nth0, Js, Axes, Ctx.index, Index),
      maplist(binder, Js, Dims, Betweens),
      phrase(( value(Parent, Ctx.put(index, Index), V0, F0),
               cast(Format, V0, F0, Item) ), Goals),
      append(Betweens, Goals, Body0),
      conjunction(Body0, Body),
      aggregate(Op, Item, Aggregate)
   },
   [aggregate_all(Aggregate, Body, Value)].

aggregate(+, Item, Aggregate) => Aggregate = sum(Item).
aggregate(<, Item, Aggregate) => Aggregate = max(Item).

:- begin_tests(ir_lower).

:- use_module(array).
:- use_module(ir).
:- use_module(buffer, [buffer_to_data/4]).

% ir_values(+C, +Device, +Tolerance, -List): the values of C, computed by
% running the IR of each kernel of its schedule on Prolog data, one data term
% per buffer, with the formats a realize under Tolerance chooses.
ir_values(C, Device, List) :-
   ir_values(C, Device, inf, List).
ir_values(C, Device, Tolerance, List) :-
   array:graph_schedule([C], Schedule0),
   fusion:fuse([C], Schedule0, Schedule),
   precision:choose_formats(Schedule, [C], Tolerance),
   foldl(run_node(Device), Schedule, [], Datas),
   data_term(C, Datas, Term),
   read_list(C, Term, List).

run_node(_, Node, Datas0, Datas), get_dict(op, Node, view(_)) =>
   Datas = Datas0.
run_node(_, Node, Datas0, Datas), get_dict(op, Node, constant(_)) =>
   Datas = Datas0.
run_node(_, Node, Datas0, Datas), get_dict(data, Node, Data), nonvar(Data) =>
   Datas = Datas0.
run_node(Device, Node, Datas0, Datas) =>
   lower_kernel(Device, Node, Node.op, Kernel, Arrays),
   ir_verify(Kernel),
   foldl(array_term, Arrays, Terms, Datas0, Datas),
   ir_run(Kernel, Terms).

% The data term of an array's buffer: its realized data, read into Prolog,
% or a fresh term for a buffer a kernel computes.
array_term(A, Term, Datas0, Datas) :-
   data_term(A, Datas0, Term),
   !,
   Datas = Datas0.
array_term(A, Term, Datas0, Datas) :-
   get_dict(data, A, Data),
   (  var(Data)
   -> functor(Term, data, A.datasize)
   ;  realized_term(A, Term)
   ),
   Datas = [Data-Term | Datas0].

data_term(A, Datas, Term) :-
   get_dict(data, A, Data),
   member(D-Term, Datas),
   D == Data,
   !.

realized_term(A, Term), get_dict(device, A, c) =>
   buffer_to_data(A.data, A.dtype(), A.datasize, Term).
realized_term(A, Term) =>
   Term = A.data.

% The elements of C, read from its buffer through its views.
read_list(C, Term, List) :-
   read_elements(C.shape(), [], C, Term, List).

read_elements([], Prefix, C, Term, Value) :-
   reverse(Prefix, Index),
   IndexExpr-_ = C.index_expr(Index),
   I is IndexExpr + 1,
   arg(I, Term, Value).
read_elements([Dim | Dims], Prefix, C, Term, List) :-
   Max is Dim - 1,
   numlist_from(0, Max, Is),
   maplist(read_at(Dims, Prefix, C, Term), Is, List).

read_at(Dims, Prefix, C, Term, I, List) :-
   read_elements(Dims, [I | Prefix], C, Term, List).

numlist_from(Low, High, List) :-
   (  High < Low
   -> List = []
   ;  numlist(Low, High, List)
   ).

% case(Name, Inputs): Inputs are the lists of the arrays graph/3 computes on.
case(chain, [[1.0, 2.0, 3.0]]).
case(compare_wide, [[70000, 3]]).
case(round, [[1.0, 2.0, -1.4]]).
case(matmul_add, [[[1, 2], [3, 4]], [[5, 6], [7, 8]], [[1, 1], [1, 1]]]).
case(sum_and_max, [[[1, 5], [4, 2]]]).
case(nested_sums, [[[[1, 2], [3, 4]], [[5, 6], [7, 8]]]]).
case(subtract_max, [[[1.0, 2.0], [3.0, 5.0]]]).
case(transpose, [[[1, 2], [3, 4]]]).
case(pad, [[1, 2]]).
case(shared, [[1, 2, 3]]).
case(float_reduce, [[[0.5, 1.5, 2.5], [3.5, 4.5, 5.5]]]).
case(float_matmul, [[[0.5, 1.5], [2.5, 3.5]], [[1.0, 0.25], [0.125, 2.0]]]).
case(comparison_sum, [[3, 1, 4, 1, 5]]).

graph(chain, [A], C) :- C @= sin(A + A) * A.
graph(compare_wide, [A], C) :- C @= ((A * A) < 1000000000).
graph(round, [A], C) :- B @= A * 2.6, C = B.as(integer).
graph(matmul_add, [A, B, X], C) :- C @= (A @ B) + X.
graph(sum_and_max, [A], C) :- C @= A.sum([1]) + A.max([1]).
graph(nested_sums, [A], C) :- B @= A.sum([2]) * 2, C = B.sum([1]).
graph(subtract_max, [A], C) :- C @= A - A.max([1], true).
graph(transpose, [A], C) :- B @= A + A, C @= B.t() + A.
graph(pad, [A], C) :- B @= A + 1, C @= B.pad([1-1]) + 1.
graph(shared, [A], C) :- B @= A * A, C @= B + B.
graph(float_reduce, [A], C) :- B @= sqrt(A), C @= B.sum([0]) * 0.5.
graph(float_matmul, [A, B], C) :- C @= A @ B.
graph(comparison_sum, [A], C) :- B @= (A < 3), C = B.sum().

input(Device, List, A) :-
   A = array{}.fromlist(List, [device(Device)]).

computed(Name, Device, C) :-
   case(Name, Inputs),
   maplist(input(Device), Inputs, Arrays),
   graph(Name, Arrays, C).

% Floats may differ in their last bits: C contracts multiply-adds, and
% reorders sums.
close_to(X, Y), is_list(X) =>
   maplist(close_to, X, Y).
close_to(X, Y), float(X) =>
   abs(X - Y) =< 1.0e-12 * max(1.0, abs(X)).
close_to(X, Y) =>
   X == Y.

test('the IR computes what the device computes',
     [forall((case(Name, _), member(Device, [prolog, c])))]) :-
   computed(Name, Device, C),
   ir_values(C, Device, Values),
   Expected = C.tolist(),
   close_to(Expected, Values).

% D is computed in float64 and rounded to the formats a tolerance chooses.
test('reduced float formats', [forall(member(T, [20, 6, 1]))]) :-
   A = array{}.fromlist([37.0, 99.0, 3.0], [device(c)]),
   B = array{}.fromlist([12.0, 98.0, 7.0], [device(c)]),
   D @= A * B,
   C @= D + A,
   ir_values(C, c, T, Values),
   Expected = C.tolist([precision(T)]),
   close_to(Expected, Values).

% A float64 array on Device holding Values, which may hold NaN: ranges can't,
% so it starts as a C buffer, with an unbounded range.
float_array(Device, Values, A) :-
   length(Values, N),
   Data =.. [data | Values],
   buffer:buffer_from_data(Buffer, float64, N, Data),
   A0 = array{}.empty([N], [device(c), dtype(float), data(Buffer),
                            format(float64)]),
   A = A0.to(Device).

nan(X) :-
   float(X),
   float_class(X, nan).

test('maxima propagate NaN', [forall(member(Device, [prolog, c]))]) :-
   current_prolog_flag(float_undefined, Undefined),
   setup_call_cleanup(set_prolog_flag(float_undefined, nan),
                      (  NaN is nan,
                         float_array(Device, [1.0, NaN, 3.0], A),
                         float_array(Device, [NaN, 1.0], B),
                         ir_values(A.max(), Device, VA),
                         ir_values(B.max(), Device, VB),
                         nan(VA),
                         nan(VB)
                      ),
                      set_prolog_flag(float_undefined, Undefined)).

:- end_tests(ir_lower).
