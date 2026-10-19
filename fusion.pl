:- module(fusion, [fuse/3, inlined_nodes//1]).

/** <module> Operator fusion

Decides which nodes of a schedule get their own kernel and buffer.

A node is *materialized* when one of the rules of materialized/2 holds: a
kernel computes it into its buffer.
Every other node is *inlined*: each kernel that reads it computes its
expression instead of loading it, so it gets neither a kernel nor a buffer.

A view is not a node of its own here: it is a way of reading the buffer of
the node it views, its *producer*.

For example, `A @ B` is `reduce(+, [2], P)` with `P = A1 * B1`, where `A1`
and `B1` are views of `A` and `B`. `P` is inlined, since only the reduce
reads it, so the schedule has a single kernel, computing
`reduce(+, [2], fused(P, A1 * B1))`.

Pipeline
--------
create_schedule/3 in array.pl runs fuse/3 right after the graph is sorted,
so the formats are chosen and the buffers allocated only for the
materialized nodes.

Inlined nodes
-------------
A kernel's op reads an inlined node as `fused(Node, Expr)`:
  * Node is the inlined array itself, for its dtype, range and format;
  * Expr is its op, whose inputs are read through the views the kernel
    reads Node through (read_through/3).

So a kernel's op is still an op term whose leaves are the arrays it loads:
`array:op_args//1` finds them through fused/2.

An inlined node has no buffer, but its value still has a format: the format
the kernel holds it in (bind_inlined_formats/1).
Its precision, computed when it was pushed, depends on that format.

Backends
--------
Each device provides, as multifile predicates of the array module:
  * expression_op(Device, Op): Op can be computed inside an expression;
  * compute_format(Device, Formats, Format): the format a kernel computes
    its inlined floats in, given the float formats of its buffers;
and compiles `fused(Node, Expr)` as the value of Expr in the format of Node.
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
% Its op isn't elementwise, or its device can't compute it inside an
% expression.
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
% Op is Op0 with each read of an inlined node replaced by fused(Node, Expr):
% Expr is the node's op, with its inputs read the way Op0 reads the node.
expr(Graph, Via, Op), is_dict(Via, array),
      producer(Via, Node), inlined(Node, Graph) =>
   mapargs(read_through(Via), Node.op, Op1),
   expr(Graph, Op1, Expr),
   Op = fused(Node, Expr).
expr(_, Via, Op), is_dict(Via, array) =>
   Op = Via.
expr(Graph, Op0, Op), compound(Op0) =>
   mapargs(expr(Graph), Op0, Op).
expr(_, Op0, Op) =>
   Op = Op0.

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

test('prolog comparison is not inlined') :-
   A = array{}.fromlist([1, 2, 3]),
   C @= (A < 2) + A,
   kernels(C, [<, +]),
   C.tolist() == [2, 2, 3].

test('c comparison is inlined') :-
   A = array{}.fromlist([1, 2, 3], [device(c)]),
   C @= (A < 2) + A,
   kernels(C, [+]),
   C.tolist() == [2, 2, 3].

:- end_tests(fusion).
