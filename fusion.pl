:- module(fusion, [fuse/3, inlined_nodes//1, node_index/3, read_shape/2]).

/** <module> Operator fusion

Decides which nodes of a schedule get their own kernel and buffer.

A node is *materialized* when one of the rules of materialized/2 holds: a
kernel computes it into its buffer.
Every other node is *inlined*: each kernel that reads it computes its
expression instead of loading it, so it gets neither a kernel nor a buffer.

A view is not a node of its own here: it is a way of reading the buffer of
the node it views, its *producer*.

For example, `A @ B + C` is `R1 + C1` where:
  * `R = reduce(+, [2], P)` and `R1` is a view of `R`;
  * `P = A1 * B1` where `A1` and `B1` are views of `A` and `B`.
`P` and `R` are inlined, since each is read once, so the schedule has a
single kernel, computing
`fused(R, reindex(R1, reduce(+, [2], fused(P, A1 * B1)))) + C1`.

Pipeline
--------
create_schedule/3 in array.pl runs fuse/3 right after the graph is sorted,
so the formats are chosen and the buffers allocated only for the
materialized nodes.

Inlined nodes
-------------
A kernel's op reads an inlined node as `fused(Node, Expr)`, where Node is
the inlined array itself, for its dtype, range and format.
Expr computes Node's op where the kernel reads it, through the view Via:
  * an elementwise op is computed at the kernel's index: Expr is the op,
    with its inputs read through Via (read_through/3);
  * a reduction loops over some axes of its own index, so it is computed at
    the index of Node that Via reads: Expr is `reindex(Via, Op)`
    (node_index/3).

So a kernel's op is still an op term whose leaves are the arrays it loads:
`array:op_args//1` finds them through fused/2 and reindex/2.

An inlined node has no buffer, but its value still has a format: the format
the kernel holds it in (bind_inlined_formats/1).
Its precision, computed when it was pushed, depends on that format.

Backends
--------
Each device provides, as multifile predicates of the array module:
  * expression_op(Device, Op): Op can be computed inside an expression;
  * compute_format(Device, Formats, Format): the format a kernel computes
    its inlined floats in, given the float formats of its buffers;
and compiles `fused(Node, Expr)` as the value of Expr in the format of Node,
`reindex(Via, Op)` at node_index/3, and a reduction by looping over the
dimensions read_shape/2 gives for its reduced axes.
*/

:- use_module(library(apply)).
:- use_module(library(dcg/high_order)).
:- use_module(array, []).

% fuse(+Outputs, +Schedule0, -Schedule)
% Schedule keeps the materialized nodes of Schedule0, and their views, in the
% same order. Each kernel of Schedule computes the inlined nodes it reads.
fuse(Outputs, Schedule0, Schedule) :-
   phrase(sequence(reads, Schedule0), Reads),
   Graph = graph(Outputs, Reads),
   include(has_buffer(Graph), Schedule0, Schedule1),
   maplist(fuse_kernel(Graph), Schedule1, Schedule).

% Materialization rules
% =====================

% materialized(+Node, +Graph)
% It is already realized.
materialized(Node, _) :-
   realized(Node).
% It is asked for.
materialized(Node, Graph) :-
   output(Node, Graph).
% Its device can't compute its op inside another kernel: rand, constant,
% contiguous and solve, or an op the device doesn't list.
materialized(Node, _) :-
   \+ array:expression_op(Node.device, Node.op).
% It is read several times: inlining would compute it once per read.
materialized(Node, Graph) :-
   \+ read_once(Node, Graph).
% It is read through a padding: a padded element must read 0, but its
% expression would compute f(0).
materialized(Node, Graph) :-
   read(Node, Graph, _, Via),
   padded(Via).
% It is a reduction that would be computed several times per element:
% inlining would redo the whole reduction each time.
materialized(Node, Graph) :-
   Node.op = reduce(_, _, _),
   repeated(Node, Graph).
% Its reader computes with buffers, not expressions.
materialized(Node, Graph) :-
   read(Node, Graph, Reader, _),
   buffer_op(Reader.op).

inlined(Node, Graph) :-
   \+ materialized(Node, Graph).

% A view has the buffer of its producer.
has_buffer(Graph, Node) :-
   producer(Node, Producer),
   materialized(Producer, Graph).

% The graph
% =========

% read(Producer, Reader, Via): the kernel computing Reader reads Producer
% through the array Via, which is Producer itself or a view of it.
reads(Reader), computed(Reader) ==>
   { phrase(array:op_args(Reader.op), Vias) },
   sequence(read_via(Reader), Vias).
reads(_) ==>
   [].

read_via(Reader, Via) -->
   { producer(Via, Producer) },
   [read(Producer, Reader, Via)].

% read(?Node, +Graph, ?Reader, ?Via)
read(Node, graph(_, Reads), Reader, Via) :-
   member(read(Producer, Reader, Via), Reads),
   same_node(Producer, Node).

read_once(Node, Graph) :-
   findall(x, read(Node, Graph, _, _), [_]).

output(Node, graph(Outputs, _)) :-
   member(Output, Outputs),
   producer(Output, Producer),
   same_node(Producer, Node).

producer(Via, Producer), get_dict(op, Via, view(Parent)) =>
   Producer = Parent.
producer(Via, Producer) =>
   Producer = Via.

same_node(A, B) :-
   A.id == B.id.

realized(Node) :-
   nonvar(Node.data).

% A node a kernel computes: it is neither realized nor a view.
computed(Node) :-
   \+ realized(Node),
   \+ get_dict(op, Node, view(_)).

padded(Via) :-
   member(View, Via.views),
   member(Dim-_-(Min-Max), View.zip()),
   \+ (Min == 0, Max == Dim).

% repeated(+Node, +Graph)
% Computing Node's readers reads an element of Node several times: one of
% them reads it through a broadcast, or is itself inlined and repeated.
repeated(Node, Graph) :-
   read(Node, Graph, _, Via),
   broadcast(Via).
repeated(Node, Graph) :-
   read(Node, Graph, Reader, _),
   inlined(Reader, Graph),
   repeated(Reader, Graph).

% A broadcast view reads an element several times along a dimension: its
% stride is 0.
broadcast(Via) :-
   member(View, Via.views),
   member(Dim-0-_, View.zip()),
   Dim > 1.

buffer_op(solve(_, _)).

% Inlining
% ========

fuse_kernel(Graph, Node, Kernel), computed(Node) =>
   expr(Graph, Node.op, Op),
   Kernel = Node.put(op, Op),
   bind_inlined_formats(Kernel).
fuse_kernel(_, Node, Kernel) =>
   Kernel = Node.

% expr(+Graph, +Op0, -Op)
% Op is Op0 with each read of an inlined node replaced by fused(Node, Expr),
% where Expr computes the node's op the way Op0 reads the node.
expr(Graph, Via, Op), is_dict(Via, array),
      producer(Via, Node), inlined(Node, Graph) =>
   inline(Graph, Via, Node, Expr),
   Op = fused(Node, Expr).
expr(_, Via, Op), is_dict(Via, array) =>
   Op = Via.
expr(Graph, Op0, Op), compound(Op0) =>
   mapargs(expr(Graph), Op0, Op).
expr(_, Op0, Op) =>
   Op = Op0.

% inline(+Graph, +Via, +Node, -Expr)
% A reduction loops over some axes of its own index, so it is computed at
% the index of Node that Via reads: reindex(Via, Op).
inline(Graph, Via, Node, Expr), get_dict(op, Node, reduce(_, _, _)) =>
   expr(Graph, Node.op, Op),
   Expr = reindex(Via, Op).
% An elementwise op is computed at the reader's index: its inputs are read
% through Via.
inline(Graph, Via, Node, Expr) =>
   mapargs(read_through(Via), Node.op, Op),
   expr(Graph, Op, Expr).

% read_through(+Via, +Input0, -Input)
% Via reads a node's buffer, which is contiguous since the node isn't
% realized: so reading Input0 as an element of the node, through Via, is
% stacking Via's views on top of Input0's.
read_through(Via, Input0, Input), is_dict(Input0, array) =>
   append(Via.views, Input0.views, [Top | Below0]),
   exclude(identity_view, Below0, Below),
   Input = Input0.push(view([Top | Below])).
read_through(_, Input0, Input) =>
   Input = Input0.

% Below the top view, a contiguous view maps a flat index to itself.
identity_view(View) :-
   View.is_contiguous() == true.

% An inlined node has no buffer, but a kernel still holds its value in some
% format: integers and booleans take their default format, and floats the
% kernel's compute format, once its buffers have formats.
bind_inlined_formats(Kernel) :-
   phrase(inlined_nodes(Kernel.op), Inlined),
   phrase(array:op_args(Kernel.op), Loads),
   include([A]>>get_dict(dtype, A, float), [Kernel | Loads], Floats),
   maplist(get_dict(format), Floats, Formats),
   maplist(bind_inlined_format(Kernel.device, Formats), Inlined).

bind_inlined_format(Device, Formats, Node), get_dict(dtype, Node, float) =>
   when(ground(Formats),
        (  array:compute_format(Device, Formats, Format),
           get_dict(format, Node, Format)
        )).
bind_inlined_format(_, _, Node) =>
   array:bind_default_format(Node).

% node_index(+Via, +ViaIndex, -Index)
% Index is the index of the node Via reads, when Via is read at ViaIndex.
% Via reads the node's buffer, which is contiguous since the node isn't
% realized.
node_index(Via, ViaIndex, Index) :-
   producer(Via, Node),
   IndexExpr-_ = Via.index_expr(ViaIndex),
   view{}.from_shape(Node.shape()) = View,
   Index = View.reverse_index_expr(IndexExpr).

% read_shape(+Operand, -Shape)
% Shape is the shape Operand is read with: the shape of the index it is
% computed at.
read_shape(A, Shape), is_dict(A, array) =>
   Shape = A.shape().
read_shape(reindex(Via, _), Shape) =>
   Shape = Via.shape().
read_shape(Op, Shape), compound(Op) =>
   arg(1, Op, A),
   read_shape(A, Shape).

% inlined_nodes(+Op)//
% The nodes Op computes inline.
inlined_nodes(fused(Node, Expr)) ==>
   [Node],
   inlined_nodes(Expr).
inlined_nodes(A), is_dict(A, array) ==>
   [].
inlined_nodes(Op), compound(Op) ==>
   { compound_name_arguments(Op, _, Args) },
   sequence(inlined_nodes, Args).
inlined_nodes(_) ==>
   [].

:- begin_tests(fusion).

:- use_module(array).

% The ops of the kernels computing Array.
kernels(Array, Ops) :-
   array:graph_schedule([Array], Schedule0),
   fuse([Array], Schedule0, Schedule),
   convlist(kernel_op, Schedule, Ops).

kernel_op(Node, Name) :-
   computed(Node),
   Node.op \= constant(_),
   functor(Node.op, Name, _).

test('matmul is one reduce kernel') :-
   A = array{}.fromlist([[1, 2], [3, 4]], [device(c)]),
   C @= A @ A,
   kernels(C, [reduce]),
   C.tolist() == [[7, 10], [15, 22]].

test('elementwise chain is one kernel') :-
   Xs = [1.0, 2.0, 3.0],
   A = array{}.fromlist(Xs, [device(c)]),
   C @= sin(A + A) * A,
   kernels(C, [*]),
   maplist([X, Y]>>(Y is sin(X + X) * X), Xs, Expected),
   Expected == C.tolist().

test('transposed read is inlined') :-
   A = array{}.fromlist([[1, 2], [3, 4]], [device(c)]),
   B @= A + A,
   C @= B.t() + A,
   kernels(C, [+]),
   C.tolist() == [[3, 8], [7, 12]].

test('node read twice is materialized') :-
   A = array{}.fromlist([1, 2, 3], [device(c)]),
   B @= A * A,
   C @= B + B,
   kernels(C, [*, +]),
   C.tolist() == [2, 8, 18].

test('rand is materialized') :-
   R = array{}.rand([4], [device(c)]),
   C @= R + R - 2*R,
   kernels(C, Ops),
   memberchk(rand, Ops),
   C.tolist() == [0.0, 0.0, 0.0, 0.0].

test('padded read is materialized') :-
   A = array{}.fromlist([1, 2], [device(c)]),
   B @= A + 1,
   C @= B.pad([1-1]) + 1,
   kernels(C, [+, +]),
   C.tolist() == [1, 3, 4, 1].

test('inlined float rounds to integer') :-
   A = array{}.fromlist([1.0, 2.0], [device(c)]),
   B @= A * 2.6,
   C = B.as(integer),
   kernels(C, [integer]),
   C.tolist() == [3, 5].

test('compute type holds inlined ranges') :-
   A = array{}.fromlist([70000, 3], [device(c)]),
   C @= ((A * A) < 1000000000),
   kernels(C, [<]),
   C.tolist() == [0, 1].

test('prolog comparison is inlined') :-
   A = array{}.fromlist([1, 2, 3]),
   C @= (A < 2) + A,
   kernels(C, [+]),
   C.tolist() == [2, 2, 3].

test('c comparison is inlined') :-
   A = array{}.fromlist([1, 2, 3], [device(c)]),
   C @= (A < 2) + A,
   kernels(C, [+]),
   C.tolist() == [2, 2, 3].

test('matmul epilogue is one kernel', [forall(member(D, [prolog, c]))]) :-
   A = array{}.fromlist([[1, 2], [3, 4]], [device(D)]),
   B = array{}.fromlist([[5, 6], [7, 8]], [device(D)]),
   C = array{}.fromlist([[1, 1], [1, 1]], [device(D)]),
   E @= (A @ B) + C,
   kernels(E, [+]),
   E.tolist() == [[20, 23], [44, 51]].

test('scaled sum is one kernel', [forall(member(D, [prolog, c]))]) :-
   A = array{}.fromlist([1.0, 2.0, 3.0], [device(D)]),
   C @= A.sum() * 2.0,
   kernels(C, [*]),
   C.tolist() == 12.0.

test('two reductions in one kernel', [forall(member(D, [prolog, c]))]) :-
   A = array{}.fromlist([[1, 5], [4, 2]], [device(D)]),
   C @= A.sum([1]) + A.max([1]),
   kernels(C, [+]),
   C.tolist() == [11, 10].

test('nested reductions are one kernel', [forall(member(D, [prolog, c]))]) :-
   A = array{}.fromlist([[[1, 2], [3, 4]], [[5, 6], [7, 8]]], [device(D)]),
   B @= A.sum([2]) * 2,
   C = B.sum([1]),
   kernels(C, [reduce]),
   C.tolist() == [20, 52].

test('broadcast reduction is materialized', [forall(member(D, [prolog, c]))]) :-
   A = array{}.fromlist([[1, 2], [3, 5]], [device(D)]),
   C @= A - A.max([1], true),
   kernels(C, Ops),
   msort(Ops, [+, reduce]),
   C.tolist() == [[-1, 0], [-2, 0]].

test('reduction read twice is materialized') :-
   A = array{}.fromlist([1, 2, 3], [device(c)]),
   S = A.sum(),
   C @= S * S,
   kernels(C, [reduce, *]),
   C.tolist() == 36.

test('inlined reduction fits the compute type') :-
   A = array{}.fromlist([4000000000, 4000000000], [device(c)]),
   C @= (A.sum() < 1),
   kernels(C, [<]),
   C.tolist() == 0.

:- end_tests(fusion).
