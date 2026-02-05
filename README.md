# Array.pl

Array.pl is a powerful library for SWI-Prolog that provides N-dimensional arrays (tensors) with an API inspired by Python's NumPy library. It is designed for performance and flexibility, featuring lazy evaluation and an extensible backend system.

## Core Features

-   **NumPy-like API**: Familiar syntax for creating and manipulating multi-dimensional arrays.
-   **Lazy Evaluation**: Operations like addition, multiplication, and reshaping build a computation graph. The actual computation is only performed when the result is explicitly requested, which allows for significant optimizations.
-   **Zero-Copy Views**: Many array manipulations (e.g., `reshape`, `transpose`, `slice`) are performed by creating a new "view" on the underlying data without copying it. This makes these operations extremely fast and memory-efficient.
-   **Extensible Backends**: The computation can be offloaded to different "devices". The default backend executes computations in pure Prolog. Future plans include a C backend for generating specialized, high-performance kernels on the fly, and an OpenCL backend for GPU acceleration.

## Getting Started

### Prerequisites

-   [SWI-Prolog](https://www.swi-prolog.org/)

### Usage

To use the library, simply load the main `array.pl` module in your Prolog code:

```prolog
:- use_module(array).
```

### Creating Arrays

```prolog
?- A = array{}.fromlist([[1, 2], [3, 4]]).
A = array{data:data(1, 2, 3, 4), ...}.

?- Z = array{}.zeros([2, 3]).
Z = array{... shape:[2,3], op:constant(0)}.

?- O = array{}.ones([3, 2]).
O = array{... shape:[3,2], op:constant(1)}.
```

### Operations

Operations are scheduled lazily. The `@=` operator is used to define an operation without immediately computing it. The actual computation is triggered when the result is requested, for example by calling `.tolist()` or `.realize()`.

```prolog
?- A = array{}.fromlist([[1,2],[3,4]]),
   B = array{}.fromlist([[5,6],[7,8]]),
   C @= A + B.

C = array{...}.

?- List = C.tolist().
List = [[6, 8], [10, 12]].
```

### Reshaping and Transposing

These operations are zero-copy and very fast.

```prolog
?- A = array{}.arange(6),
   ListA = A.tolist().
ListA = [0, 1, 2, 3, 4, 5].

?- B = A.reshape([2, 3]),
   ListB = B.tolist().
ListB = [[0, 1, 2], [3, 4, 5]].

?- C = B.transpose(),
   ListC = C.tolist().
ListC = [[0, 3], [1, 4], [2, 5]].
```

### Reductions

```prolog
?- A = array{}.fromlist([[1,2,3],[4,5,6]]),
   S @= A.sum(),
   SumValue = S.tolist().
SumValue = 21.

?- M @= A.max([1]), % Max along axis 1
   MaxValues = M.tolist().
MaxValues = [3, 6].
```

## Architecture

Array.pl's power comes from a few core concepts:

-   **`array{}`**: The primary data structure, a Prolog dict representing an N-dimensional array. It contains metadata like shape, data type, and the operation that defines it.
-   **`view{}`**: A dict that defines how to interpret the underlying data. It holds shape, strides, offset, and mask information. An `array` can have a stack of views, allowing for complex, non-contiguous memory layouts without data duplication.
-   **`op`**: An operation in the computation graph. It can be a simple constant (`constant(0)`), a transformation on a parent array (`reshape(Parent)`), or an element-wise operation on multiple arrays (`elementwise(+, [A, B])`).
-   **Schedule**: When an array needs to be computed (e.g., by calling `.tolist()` or `.realize()`), Array.pl creates a `schedule` by performing a topological sort of the dependency graph. This schedule is then compiled and executed by the target `device`.
-   **Device**: A backend responsible for compilation and execution. The default is `prolog`, which generates and runs Prolog code.

## Development

### Running Tests

To run the built-in test suites, use the following command from the project root:

```bash
swipl -g "load_files([array, view, runtime_prolog]), run_tests" -t halt
```

## Roadmap

-   [ ] Implement more NumPy operators and functions.
-   [ ] Add support for `clpBNR` as a data type and backend.
-   [ ] Develop a C backend for JIT compilation of high-performance compute kernels.
-   [ ] Explore an OpenCL backend for GPU and parallel computation.
