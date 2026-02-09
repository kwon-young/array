# Refactoring and Bug Fixes Plan

This document outlines the planned refactoring work to separate runtime-specific code and fix identified bugs, particularly concerning the data type system.

## 1. Refactor Prolog Runtime Specifics

The `array.pl` module contains code that is specific to the Prolog runtime. This should be moved to `runtime_prolog.pl` to prepare for adding other runtimes (e.g., a C runtime).

### Code to be moved from `array.pl` to `runtime_prolog.pl`:

-   **Execution Logic**:
    -   `allocate_schedule/1` and `allocate/1` (which use Prolog-specific term creation).
    -   compile the schedule so that it is a simple predicate call
-   **Data Access and Conversion**:
    -   `M.fromlist/1-2` and `M.tolist/1` (which rely on Prolog compound terms for data storage).
    -   `M.index_input/2` (which generates code using `arg/3` to access elements).
    -   `M.to/1` (device transfer logic).
-   **Type System**:
    -   `dtype/3` predicate.
    -   `broadcast_dtype/3` predicate.
    -   The part of `push(constant(...), ...)` that infers dtype from a constant value.

## 3. Improve Dtype Handling

The current data type (dtype) handling has several weaknesses that need to be addressed.

-   **Reduce Operations**: The result of `sum` or `max` operations currently defaults to `float`. It should preserve the dtype of the input array. For example, summing an `integer` array should result in an `integer` array.
-   **Comparison Operations**: Operations like `A < B` produce boolean results but currently return an array with the same dtype as the inputs (e.g., `float`). The output dtype should be `boolean` or `integer`.
-   **Inconsistent `dtype` Option**: In `M.full/3`, providing a `dtype` in the options acts as a type check, not a cast. This should be changed to cast the fill value to the specified `dtype`.
-   **Inefficient Type Inference**: `M.fromlist` infers the dtype by promoting from `boolean` upwards. This is inefficient if the list contains higher-precision types like `float`. The inference should be more direct.
-   **Hardcoded Dtypes in Helpers**: `M.zeros` and `M.ones` create arrays with the default `float` dtype. They should infer the dtype from the value (i.e., `integer`).
