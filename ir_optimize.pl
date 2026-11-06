:- module(ir_optimize, [optimize_kernel/3, ir_optimize/3]).

/** <module> Optimizing the kernel IR

A kernel clause is added to an e-graph of library(egraph) as it is, then
saturated with layers of rules, then extracted (docs/kernel_ir.md). A layer
is a list of module-qualified rules, saturated together; layers run in
order. Each device gives its own layers with layers/2.
*/

:- use_module(library(apply)).
:- use_module(library(egraph)).

:- multifile layers/2.

% layers(?Device, -Layers): the layers of rules Device optimizes its kernels
% with.

% optimize_kernel(+Device, +Kernel0, -Kernel)
% Kernel is Kernel0 optimized with the layers of Device, or Kernel0 itself
% for a device without layers.
optimize_kernel(Device, Kernel0, Kernel) :-
   device_layers(Device, Layers),
   ir_optimize(Layers, Kernel0, Kernel).

device_layers(Device, Layers), layers(Device, Layers0) =>
   Layers = Layers0.
device_layers(_, Layers) =>
   Layers = [].

% ir_optimize(+Layers, +Kernel0, -Kernel)
% Kernel is Kernel0 saturated with each of Layers, then extracted. The same
% kernel recurs in every realize computing it: it is optimized once.
:- table ir_optimize/3.

ir_optimize(Layers, Kernel0, Kernel),
      phrase(optimized(Layers, Kernel0, Kernel1), [], _) =>
   Kernel = Kernel1.
% a merge of two classes found their values different: a rule is wrong
ir_optimize(Layers, _, _) =>
   throw(error(ir_error(optimization_failed, Layers), _)).

optimized(Layers, Kernel0, Kernel) -->
   add_term(Kernel0, Id),
   foldl(saturate_layer, Layers),
   extract(Id, Kernel).

% saturate_layer(+Rules)//
% library(egraph) doesn't count a property set on a class as a change, so a
% saturation can stop before a rule reading that property fires: a pass is
% repeated until neither the nodes nor the properties change, at most
% max_passes/1 times.
saturate_layer(Rules) -->
   { max_passes(N) },
   passes(Rules, N).

max_passes(32).

passes(_, 0, Graph0, Graph) =>
   Graph = Graph0.
passes(Rules, N, Graph0, Graph) =>
   fingerprint(Graph0, Before),
   saturate(Rules, 1, Graph0, Graph1),
   fingerprint(Graph1, After),
   N1 is N - 1,
   next_pass(Before, After, Rules, N1, Graph1, Graph).

next_pass(Same, Same, _, _, Graph0, Graph) =>
   Graph = Graph0.
next_pass(_, _, Rules, N, Graph0, Graph) =>
   passes(Rules, N, Graph0, Graph).

% The number of nodes and properties of an e-graph. A property is an
% attribute of a class id.
fingerprint(Graph, Nodes-Properties) :-
   length(Graph, Nodes),
   foldl(node_properties, Graph, 0, Properties).

node_properties(_-node(Id, _), N0, N) :-
   class_properties(Id, K),
   N is N0 + K.

class_properties(Id, N), get_attrs(Id, Attributes) =>
   attributes_count(Attributes, N).
class_properties(_, N) =>
   N = 0.

attributes_count([], N) =>
   N = 0.
attributes_count(att(_, _, Attributes), N) =>
   attributes_count(Attributes, N0),
   N is N0 + 1.
