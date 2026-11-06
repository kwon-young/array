:- module(ir_index, []).

/** <module> Index simplification rules of the kernel IR

Rules of library(egraph) simplifying the index arithmetic of a kernel clause,
for ir_optimize.pl. They only do what a C compiler can't: removing a `//` or
a `mod` whose result depends on the range of its operands. Identities,
constants and strength reduction are left to the compiler.

One layer, saturated: the analyses, the rewrites and materialize/5.

Two properties, on the classes of index arithmetic only:
  * fd(V): V is a clpfd variable equal to the value of the class;
  * divisor(S): S divides every value of the class.
A rule only matches classes having fd: values, whose arithmetic may be
inexact, are never rewritten. Rules guard on non-negative operands, where
`//` and `mod` agree with C's `/` and `%`. A guard reads a property value
and tests it, without unifying it.
*/

:- use_module(library(clpfd)).
:- use_module(library(egraph)).

% Properties
% ==========

% Two equal classes have the intersection of their domains.
egraph:merge_property(fd, V1, V2, V) :-
   V1 = V2,
   V = V1.
egraph:merge_property(divisor, S1, S2, S) :-
   S is lcm(S1, S2).

% Analyses
% ========

egraph:analyze(fd_int, '$NODE'(N), [\+ fd(_)], [fd(N), divisor(S)]) :-
   integer(N),
   S is abs(N).
egraph:analyze(fd_between, between(L, H, I),
               [fd(L, VL), fd(H, VH), \+ fd(I, _)],
               [fd(I, V), divisor(I, 1)]) :-
   V in VL..VH.
egraph:analyze(fd_add, A+B,
               [fd(A, VA), fd(B, VB), divisor(A, SA), divisor(B, SB), \+ fd(_)],
               [fd(V), divisor(S)]) :-
   V #= VA + VB,
   S is gcd(SA, SB).
egraph:analyze(fd_mul, A*B,
               [fd(A, VA), fd(B, VB), divisor(A, SA), divisor(B, SB), \+ fd(_)],
               [fd(V), divisor(S)]) :-
   V #= VA * VB,
   S is SA * SB.
egraph:analyze(fd_div, A//K, [fd(A, VA), fd(K, VK), \+ fd(_)], [fd(V), divisor(1)]) :-
   V #= VA // VK.
egraph:analyze(fd_mod, A mod K, [fd(A, VA), fd(K, VK), divisor(A, SA), \+ fd(_)],
               [fd(V), divisor(S)]) :-
   mod_value(VA, VK, SA, V, S).

% A multiple of K is 0 modulo K.
mod_value(VA, VK, SA, V, S), multiple(SA, VK), nonneg(VA) =>
   V = 0,
   S = 0.
mod_value(VA, VK, _, V, S) =>
   V #= VA mod VK,
   S = 1.

% Rewrites
% ========

egraph:rewrite(add_assoc, (A+B)+C, [fd(A, _), fd(B, _), fd(C, _)], A+(B+C), []).
egraph:rewrite(add_comm, A+B, [fd(A, _), fd(B, _)], B+A, []).
% The multiple of K in a sum goes through the division and the modulo.
egraph:rewrite(div_split, (A+B)//K,
               [divisor(A, S), fd(A, VA), fd(B, VB), fd(K, VK)],
               A//K + B//K, []) :-
   multiple(S, VK),
   nonneg(VA),
   nonneg(VB).
egraph:rewrite(mod_split, (A+B) mod K,
               [divisor(A, S), fd(A, VA), fd(B, VB), fd(K, VK)],
               B mod K, []) :-
   multiple(S, VK),
   nonneg(VA),
   nonneg(VB).
egraph:rewrite(mod_small, A mod K, [fd(A, VA), fd(K, VK)], A, []) :-
   integer(VK),
   nonneg(VA),
   fd_sup(VA, Max),
   Max < VK.

% Constants
% =========

% A class whose value is known holds that number, so all classes of one
% value are a single class. This keeps saturation finite: rewrites derive
% equalities such as X = 0+X, and associativity would otherwise build the
% classes 0+0, (0+0)+0... without end. As a leaf of cost 0, the number beats
% any other node of its class. '$NODE'(_) matches every class: a bare
% variable pattern would match none.
egraph:rule(materialize, ['$NODE'(_)-Id], [fd(Id, V)], ['$NODE'(V)-Id], [cost(V, 0)]) :-
   integer(V).

% Guards
% ======

multiple(S, K) :-
   integer(K),
   K > 0,
   S mod K =:= 0.

nonneg(V) :-
   fd_inf(V, Min),
   Min >= 0.

:- begin_tests(ir_index).

:- use_module(library(aggregate)).
:- use_module(library(random)).
:- use_module(ir, [ir_run/2, ir_verify/1]).
:- use_module(ir_optimize, [ir_optimize/3]).
:- use_module(array).
:- use_module(ir_lower, [lower_kernel/5]).

layers([[ir_index:fd_int, ir_index:fd_between, ir_index:fd_add, ir_index:fd_mul,
         ir_index:fd_div, ir_index:fd_mod,
         ir_index:add_assoc, ir_index:add_comm, ir_index:div_split,
         ir_index:mod_split, ir_index:mod_small, ir_index:materialize]]).

optimized(Kernel0, Kernel) :-
   layers(Layers),
   ir_optimize(Layers, Kernel0, Kernel).

% The number of divisions and modulos left in Term that a C compiler can't
% remove: it removes (X*C)//K when K divides C.
divisions(Term, N) :-
   aggregate_all(count, (sub_term(T, Term), compound(T), division(T)), N).

division(_ mod _).
division(X // K) :-
   \+ multiple_division(X, K).

multiple_division(_*C, K) :-
   integer(C),
   integer(K),
   C mod K =:= 0.

matmul_raw((kernel(O-float64, A-float64, B-float64) :-
   forall(( between(0, 1, I1), between(0, 1, I2) ),
          ( aggregate_all(sum(VA*VB),
               ( between(0, 1, T),
                 load(A-float64,
                      ((I1*2 + I2)//2*4 + (I1*2 + I2) mod 2*2 + T)//4*2
                      + ((I1*2 + I2)//2*4 + (I1*2 + I2) mod 2*2 + T) mod 4//2*0
                      + ((I1*2 + I2)//2*4 + (I1*2 + I2) mod 2*2 + T) mod 4 mod 2*1,
                      VA),
                 load(B-float64,
                      ((I1*2 + I2)//2*4 + (I1*2 + I2) mod 2*2 + T)//4*0
                      + ((I1*2 + I2)//2*4 + (I1*2 + I2) mod 2*2 + T) mod 4//2*1
                      + ((I1*2 + I2)//2*4 + (I1*2 + I2) mod 2*2 + T) mod 4 mod 2*2,
                      VB) ),
               S),
            store(O-float64, I1*2 + I2, S) )))).

test('a matmul has no division left for the compiler', [timeout(10)]) :-
   matmul_raw(Kernel0),
   optimized(Kernel0, Kernel),
   divisions(Kernel, N),
   N == 0,
   ir_verify(Kernel),
   O = data(_, _, _, _),
   ir_run(Kernel, [O, data(1.0, 2.0, 3.0, 4.0), data(5.0, 6.0, 7.0, 8.0)]),
   O == data(19.0, 22.0, 43.0, 50.0).

test('optimizing binds nothing', [timeout(10)]) :-
   matmul_raw(Kernel0),
   copy_term(Kernel0, Copy),
   optimized(Kernel0, _),
   Kernel0 =@= Copy.

test('a dimension of size 1 gets the index 0', [timeout(10)]) :-
   Kernel0 = (kernel(O-uint8, A-uint8) :-
                 forall(( between(0, 2, I), between(0, 0, J) ),
                        ( load(A-uint8, I*1 + J*3, V),
                          store(O-uint8, I + J, V) ))),
   optimized(Kernel0, Kernel),
   Kernel = (_ :- forall((between(0, 2, I1), between(0, 0, J1)), _)),
   I1 == I,
   J1 == 0,
   ir_verify(Kernel).

% mod_small and mod_split derive J = 0+J: saturation ends only because the
% classes of 0, 0+0... are one.
test('an index equal to 0 plus itself saturates', [timeout(5)]) :-
   Kernel0 = (kernel(O-uint8, A-uint8) :-
                 forall(between(0, 1, J),
                        ( load(A-uint8, (0 + J) mod 2, V),
                          store(O-uint8, J, V) ))),
   optimized(Kernel0, Kernel),
   Kernel = (_ :- forall(_, (load(_, Index, _), _))),
   Index == J.

test('values are not rewritten', [timeout(10)]) :-
   Kernel0 = (kernel(O-float64, A-float64) :-
                 forall(between(0, 1, I),
                        ( load(A-float64, I, V),
                          store(O-float64, I, V + 0) ))),
   optimized(Kernel0, Kernel),
   Kernel = (_ :- forall(_, (_, store(_, _, Value)))),
   Value == V + 0.

% Random views: permuted, merged by a reshape, then summed or added to.
random_graph(C) :-
   random_between(2, 4, NDim),
   length(Shape, NDim),
   maplist(random_between(1, 4), Shape),
   foldl(times, Shape, 1, Size),
   numlist(1, Size, List),
   A = array{}.fromlist(List, [device(c)]).reshape(Shape),
   Last is NDim - 1,
   numlist(0, Last, Axes),
   random_permutation(Axes, Permutation),
   P = A.permute(Permutation),
   Before is NDim - 2,
   random_between(0, Before, K),
   merged_shape(P.shape(), K, Merged),
   B = P.reshape(Merged),
   random_member(Tail, [sum, add]),
   tail(Tail, B, C).

tail(sum, B, C) :-
   length(B.shape(), NDim),
   Last is NDim - 1,
   random_between(0, Last, Axis),
   C @= B.sum([Axis]).
tail(add, B, C) :-
   C @= B + 1.

times(D, S0, S) :-
   S is S0*D.

% Shape with the dimensions K and K+1 of Shape0 merged.
merged_shape(Shape0, K, Shape) :-
   length(Prefix, K),
   append(Prefix, [D1, D2 | Suffix], Shape0),
   D is D1*D2,
   append(Prefix, [D | Suffix], Shape).

% The kernels of C's schedule.
kernel(C, Kernel, Arrays) :-
   array:graph_schedule([C], Schedule0),
   fusion:fuse([C], Schedule0, Schedule),
   precision:choose_formats(Schedule, [C], inf),
   member(Node, Schedule),
   \+ get_dict(op, Node, view(_)),
   \+ get_dict(op, Node, constant(_)),
   get_dict(data, Node, Data),
   var(Data),
   lower_kernel(c, Node, Node.op, Kernel, Arrays).

random_data(A, Term) :-
   Size = A.datasize,
   functor(Term, data, Size),
   forall(between(1, Size, I),
          ( random_between(0, 3, V), nb_setarg(I, Term, V) )).

same_values(Kernel0, Kernel, [Out | Inputs]) :-
   maplist(random_data, Inputs, Datas),
   Size = Out.datasize,
   functor(O0, data, Size),
   functor(O, data, Size),
   ir_run(Kernel0, [O0 | Datas]),
   ir_run(Kernel, [O | Datas]),
   O0 == O.

test('random views compute the same values', [timeout(60)]) :-
   set_random(seed(42)),
   forall(between(1, 50, _),
          ( random_graph(C),
            forall(kernel(C, Kernel0, Arrays),
                   ( optimized(Kernel0, Kernel),
                     ir_verify(Kernel),
                     same_values(Kernel0, Kernel, Arrays) )) )).

:- end_tests(ir_index).
