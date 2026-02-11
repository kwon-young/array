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

### Dtype Precedence Rules for Array Creation from a Value

When creating an array from a value (e.g., with `M.full`, `M.zeros`), the `dtype` is determined by the following rules of precedence:

1.  **Explicit `dtype` in `Options`**: If the `Options` list contains `dtype(T)`, the resulting array's `dtype` is `T`. A type check must ensure the provided value is compatible with `T`.
2.  **Inherited `dtype` from Source Array**: If no `dtype` is in `Options`, the `dtype` is inherited from the source array `M`. This provides `numpy.*_like` behavior. A type check must ensure the value is compatible with `M.dtype`.
3.  **Inferred `dtype` from Value**: As a fallback (e.g., when calling `array{}.full(...)`), the `dtype` is inferred from the natural type of the value.

-   **Inconsistent `dtype` Option**: In `M.full/3`, providing a `dtype` in the options acts as a type check, not a cast. This should be changed to cast the fill value to the specified `dtype`.
-   **Inefficient Type Inference**: `M.fromlist` infers the dtype by promoting from `boolean` upwards. This is inefficient if the list contains higher-precision types like `float`. The inference should be more direct.
-   **Hardcoded Dtypes in Helpers**: `M.zeros` and `M.ones` create arrays with the default `float` dtype. They should infer the dtype from the value (i.e., `integer`).
