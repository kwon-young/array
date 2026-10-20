# Kernel IR

Status: draft.

## Goals

- One generic representation of a kernel, between the fused array graph and
  the backends. C, OpenCL and Prolog each lower it to their own dialect.
- The target of kernel optimizations: rule sets saturated on an e-graph, some
  generic, some specific to a dialect.
- Executable: a kernel is a Prolog clause, which runs once asserted, given
  three helper predicates. Running it gives the reference semantics of every
  kernel, and of every optimization: an optimized kernel must compute what
  the original computes.
- Pure, apart from the store: no accumulators, no counters, no `+=`.
  Equality saturation needs terms whose meaning doesn't depend on an order of
  side effects. Mutation only appears when a dialect lowers the IR.

## Where it sits

```
push (build the graph)
  → graph_schedule → fuse → choose_formats → allocation
  → lower each kernel to the IR             (index_expr is only called here)
  → optimize the IR: saturate the enabled rule sets, extract
  → lower the IR to the dialect, print, compile
```

Today, each backend generates its code straight from the fused op
(`kernel_c:value//3`, `runtime_prolog:value//3`). The IR splits this into a
single lowering to the IR, and one printer per dialect.

## The kernel clause

A kernel is a clause:

```prolog
kernel(Out-Format0, In1-Format1, ..., InN-FormatN) :-
   Body.
```

- Its arguments are its buffers, each paired with its format: the outputs
  first, then the inputs. The pair is the buffer's name everywhere in the
  kernel: its accesses use the same term, `In1-Format1`.
- `Body` ranges over the output's domain, a `forall` over a `between` per
  dimension, and stores every element. The domain is part of the kernel:
  calling the clause computes the whole output, the output indices get
  their bounds from their binders like any index variable, and schedule
  decisions such as `parallel/1` apply to it. Calling a function per element,
  as C does, is how a dialect prints the domain, not part of the IR.
- Its name is `kernel` until it is registered, then the hash of the clause,
  as kernels are named today.

## Vocabulary

| goal | meaning |
|---|---|
| `forall(Domain, Goal)` | runs `Goal` for each solution of `Domain` |
| `between(0, Max, I)` | binds the index variable `I` to `0..Max` |
| `load(Buffer-Format, Index, Value)` | `Value` is the element `Index` of `Buffer` |
| `store(Buffer-Format, Index, Value)` | writes `Value` as the element `Index` of `Buffer` |
| `Value is Expr` | arithmetic |
| `cast(Format, In, Out)` | `Out` is `In` in `Format` |
| `( Cond -> Then ; Else )` | `Cond` is a conjunction of index comparisons |
| `aggregate_all(sum(X), Goal, Sum)` | sum of `X` over the solutions of `Goal` |
| `aggregate_all(max(X), Goal, Max)` | maximum of `X` over the solutions of `Goal` |
| annotations | see [Annotations](#annotations) |

Index expressions, the arguments `Index` and the operands of index
comparisons, use `+`, `*`, `//`, `mod`, integer constants and index variables.
Every index value is non-negative, so `//` and `mod` agree with C's `/` and
`%`.

Reductions are `aggregate_all/3` with its Prolog semantics, which is the
reference:

- a sum over an empty domain is 0;
- a maximum propagates NaN, as numpy's `max` does: dialects must lower it to
  agree, not to C's `if (acc < x) acc = x`, which ignores a NaN unless it
  comes first;
- a maximum over an empty domain never reaches the IR: like numpy, the array
  library rejects a maximum over a zero-size axis when it is pushed, since a
  maximum has no identity. `aggregate_all(max(...))` failing on an empty
  domain is then never observed.

Value expressions, in `is`, use `+`, `*`, `sin`, `log`, `sqrt`, constants,
`float`, `integer` and `random_float`. A comparison producing a value is a
conditional: `( A < B -> V = 1 ; V = 0 )`.

## Reference semantics

The helper predicates, for buffers that are Prolog `data(...)` terms:

```prolog
load(Buffer-_Format, Index, Value) :-
   I is Index + 1,
   arg(I, Buffer, Value).

store(Buffer-_Format, Index, Value) :-
   I is Index + 1,
   nb_setarg(I, Buffer, Value).

cast(Format, In, Out), float_format(Format) =>
   round_to_format(Format, In, Out).
cast(_, In, Out) =>
   Out is integer(In).

% A value rounds to a float format as C converts it, to the nearest with
% ties to even: through a one-element C buffer of buffer.pl.
round_to_format(Format, In, Out) :-
   buffer_from_data(Buffer, Format, 1, data(In)),
   buffer_to_data(Buffer, Format, 1, data(Out)).

float_format(float16).
float_format(float32).
float_format(float64).
```

A kernel runs by asserting its clause and calling it on data, paired with
formats or with free variables:

```prolog
?- assertz((kernel(O-uint8, B-uint8) :- …)),
   O = data(_, _, _, _),
   kernel(O-uint8, data(2, 3)-_).
```

Casts:

- To a float format, a value rounds to the nearest, ties to even. Going
  through a C buffer makes the reference agree with the C and OpenCL
  conversions by construction. It agrees with numpy too, including ties
  (`16777217` → `16777216.0` in `float32`), overflow (`65520.0` → `inf` in
  `float16`) and subnormals (`6.0e-8` → `5.960464477539063e-08` in
  `float16`).
- To an integer format, a value rounds like Prolog's `integer/1`: to the
  nearest, ties away from zero, as the C backend's `round()`. numpy's
  `astype` truncates instead; the array library rounds on purpose.
- The value of a cast always fits its format: ranges guarantee it, since the
  format was chosen to hold the range. A cast never wraps.
- Booleans come from conditionals, never from a cast.

## Outputs

- A buffer the body stores into is an output; a buffer it loads is an input.
- No buffer is both loaded and stored in one kernel: there is no update in
  place. The buffer pool guarantees it, since an input keeps its memory
  until its reader has run, and it is also what makes C's `restrict`
  correct.
- Every element of an output is stored exactly once.

Together, these make the body independent of the order of its stores and
loads, which equality saturation needs. A kernel may have several outputs:
several stores in one `forall` when they share a domain, or a conjunction of
`forall`s otherwise.

## Variables, scope and bounds

- Every variable is assigned once: by its binder (`between`), a `load`, an
  `is`, a `cast`, a conditional or an `aggregate_all`.
- An index variable is bound by `between(0, Max, I)`, which also gives its
  bounds: `0 =< I =< Max`. Optimizations read bounds from the binders.
- The only variables shared with the outside are the head's buffers.

## Formats

Every value has a format. Printers need it to declare variables, and the
precision model needs it to round.

- A buffer's format is in its pair, `Buffer-Format`, in the head and in each
  of its accesses: an access is self-contained for a rule, and the head is
  the signature printers need. The e-graph shares the repeated pair as one
  class. A verifier checks that a buffer variable has a single format.
- `load` gives the format of the buffer.
- `cast(Format, _, Out)` gives `Format`.
- `is` gives the format of its operands. The lowering inserts casts so that
  the operands of an operation share a format: this is today's `load_types`,
  made explicit.
- A conditional producing a comparison gives `bool`.
- An index variable is an integer of the dialect's index type.

## Annotations

Annotations carry schedule decisions: how a dialect should run a part of a
kernel, not what it computes. An annotation is a goal that wraps another one,
and runs it unchanged:

```prolog
simd(Goal) :- call(Goal).
parallel(Goal) :- call(Goal).
```

So an annotated kernel still executes, and gives the same values. Printers
read annotations: `simd(aggregate_all(sum(X), G, S))` prints as a C loop with
`#pragma omp simd reduction(+:S)`, and `parallel(forall(D, G))` maps the
domain `D` to OpenCL work items.

## Examples

### `(A @ B) + X`, 2×2, fused into one kernel

As the lowering produces it, with the indices composed from the views:

```prolog
kernel(O-float64, A-float64, B-float64, X-float64) :-
   forall(( between(0, 1, I1), between(0, 1, I2) ),
          ( aggregate_all(sum(P),
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
                      VB),
                 P is VA*VB ),
               S),
            load(X-float64, I1*2 + I2, VX),
            V is S + VX,
            store(O-float64, I1*2 + I2, V) )).
```

After index simplification:

```prolog
kernel(O-float64, A-float64, B-float64, X-float64) :-
   forall(( between(0, 1, I1), between(0, 1, I2) ),
          ( aggregate_all(sum(P),
               ( between(0, 1, T),
                 load(A-float64, I1*2 + T, VA),
                 load(B-float64, T*2 + I2, VB),
                 P is VA*VB ),
               S),
            load(X-float64, I1*2 + I2, VX),
            V is S + VX,
            store(O-float64, I1*2 + I2, V) )).
```

### A padded read: `B.pad([1-1]) + 1`

```prolog
kernel(O-uint8, B-uint8) :-
   forall(between(0, 3, I),
          ( ( 1 =< I, I < 3 -> load(B-uint8, I - 1, VB) ; VB = 0 ),
            V is VB + 1,
            store(O-uint8, I, V) )).
```

### A comparison: `(A * A) < 1000000000`, with an inlined uint32 product

```prolog
kernel(O-bool, A-uint32) :-
   forall(between(0, 1, I),
          ( load(A-uint32, I, VA0),
            cast(uint64, VA0, VA),
            P0 is VA*VA,
            cast(uint64, P0, P),
            ( P < 1000000000 -> V = 1 ; V = 0 ),
            store(O-bool, I, V) )).
```

The product is inlined: `cast(uint64, P0, P)` is its rounding to its own
format, today's `fused/2`. The load's cast to `uint64` is today's compute
type.

### A maximum of floats rounded to integers: `(A * 2.0).as(integer).max([1])`

```prolog
kernel(O-int8, A-float64) :-
   forall(between(0, 1, I),
          ( aggregate_all(max(X),
               ( between(0, 1, J),
                 load(A-float64, I*2 + J, VA),
                 P is VA*2.0,
                 cast(int8, P, X) ),
               M),
            store(O-int8, I, M) )).
```

### Nested reductions: `(A.sum([2]) * 2).sum([1])`

```prolog
kernel(O-uint8, A-uint8) :-
   forall(between(0, 1, I),
          ( aggregate_all(sum(Y),
               ( between(0, 1, J),
                 aggregate_all(sum(X),
                    ( between(0, 1, K),
                      load(A-uint8, I*4 + J*2 + K, X) ),
                    S0),
                 Y is S0*2 ),
               S),
            store(O-uint8, I, S) )).
```

### `rand`

```prolog
kernel(O-float64) :-
   forall(between(0, 3, I),
          ( V is random_float,
            store(O-float64, I, V) )).
```

`random_float` isn't pure: rules must never duplicate or remove it.

## From the fused graph to the IR

One lowering replaces both `value//3`:

- a kernel's output domain is `forall` over `between(0, Dim-1, I)` for each
  dimension of the output;
- a materialized input is a `load`, at the index `index_expr` composes from
  its views, guarded by its validity condition when the views mask it;
- a `fused(Node, Expr)` is `Expr`'s goals, then a `cast` to `Node`'s format;
- `reindex(Via, Expr)` computes `Expr` with the index of the node `Via`
  reads;
- a reduction is `aggregate_all` over `between` for each reduced axis;
- `float` and `integer` ops are `cast`s;
- constants are numbers in expressions.

`index_expr` and `node_index` are called here only, and their results are
the raw index terms the optimizations simplify.

## Optimizing

The kernel clause is added to an e-graph as it is: head, goals, expressions
and variables. Optimizations are rule sets in the syntax of
`library(egraph)`, saturated together; a pipeline is the list of enabled
rule names, which may depend on the target dialect.

Conventions for rules:

- A rule never binds a variable of the kernel. Guards compare with `==`,
  `\==` and the analysis properties.
- Constants and bounds are properties, not rewrites. The bounds of an index
  variable come from its binder: an analysis on `between(L, H, V)` gives the
  class of `V` the bounds `L..H`. Bounds flow through `+`, `*`, `//` and `mod`
  as clpfd domains.
- No rule may duplicate or drop an impure expression (`random_float`) or a
  `store`.

Examples of rule sets:

- index simplification: `//` and `mod` folding under bounds, on `load` and
  `store` indices;
- validity: a condition proven by bounds turns `( Cond -> Then ; Else )` into
  `Then`;
- formats: a `cast` to the format a `load` already has is removed;
- C schedule: wrap a sum in `simd/1`;
- OpenCL schedule: wrap the output `forall` in `parallel/1`.

## Lowering to dialects

| IR | C | OpenCL | Prolog |
|---|---|---|---|
| head | kernel function and runtime predicate, typed from the pairs | `__kernel` function, typed from the pairs | the clause itself |
| output `forall` | runtime loops calling the kernel function | `get_global_id` | `forall` |
| `between` in a reduction | `for` loop | `for` loop | `between` |
| `load`, `store` | `a1[Index]`, `a0[Index] = V` | same | `arg/3`, `nb_setarg/3` |
| `X is E` | `T X = E;` with `T` the format of `X` | same | `X is E` |
| `cast(F, I, O)` | `T O = (T)I;` (`round` from a float to an integer) | same | `round_to_format` or `integer` |
| conditional | `if`/`else`, or `?:` for values | same | `->` |
| `aggregate_all(sum(X), G, S)` | `S = 0; for (…) S += X;` | same | `aggregate_all` |
| `simd(G)` | `#pragma omp simd reduction(…)` | — | `call` |
| `parallel(G)` | — | work items | `call` |

## Testing

The examples above run as written, once asserted. With `B = data(2, 3)`, the
padded read stores `data(1, 3, 4, 1)`. With `A = data(1, 2, 3, 4)`,
`B = data(5, 6, 7, 8)` and `X = data(1, 1, 1, 1)`, both versions of the
matmul store `data(20, 23, 44, 51)`.

- Each backend's kernels agree with running the IR on the same inputs.
- For each rule set: running the IR before and after saturation gives the
  same values, on random inputs.

