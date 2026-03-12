Priority: Medium

# Add C-based runtime

Plan and implement the addition of a new C-based runtime (`runtime_c.pl`). This will allow compiling and executing array operations using a C backend instead of the Prolog one to improve performance.

Depends on the completion of the Prolog runtime factoring.

## Technical Requirements

1. **Compilation & Invocation**:
   - Generate C source code into a temporary file.
   - Compile the generated C code into a shared library (`.so`, `.dll`, or `.dylib` depending on the platform) using standard system compilers (e.g., `gcc` or `clang`) with `-O3 -shared -fPIC` flags.
   - Load and invoke the compiled functions dynamically using SWI-Prolog's `ffi` pack.

2. **Memory Management**:
   - Prolog will remain the owner of the array memory.
   - Arrays will be allocated in Prolog, and their underlying data buffers (e.g., as blobs or packed byte arrays) will be passed to the C functions as raw pointers.

3. **Operations Subset**:
   - Start with basic elementwise operations: arithmetic (`+`, `-`, `*`), comparisons (`<`, `<=`, etc.), and basic math (`sin`, `cos`, `log`, `sqrt`).
   - Implement basic reduction operations (`sum`, `max`).
   - Matrix operations like `solve` can be deferred to a later iteration or mapped to existing BLAS/LAPACK bindings if available, but for now, throw an unsupported error.

4. **Data Types (DTypes)**:
   - Support `boolean` (as `uint8_t` or `bool`), `integer` (as `int64_t`), and `float` (as `double`).
   - The Prolog `rational` dtype is **unsupported** in the C runtime. Attempting to compile a C kernel with a `rational` tensor should throw a `domain_error(c_runtime_unsupported_dtype, rational)`.

5. **Index Math & Views**:
   - The generated C code must replicate the `view` index flattening and validation logic natively. C functions should take flat offsets, shapes, and strides to compute physical indices internally within the C loops, allowing for maximum optimization by the C compiler.

## Acceptance Criteria
- [ ] `runtime_c.pl` is implemented and can be selected by passing `device(c)` to array creation options.
- [ ] Elementwise operations compile and execute correctly, producing the exact same results as the `prolog` device.
- [ ] Reductions (`sum`, `max`) compile and execute correctly.
- [ ] C code is correctly generated, compiled, and dynamically loaded at runtime without memory leaks from the shared library handles.
- [ ] Attempting to use the `rational` dtype with the `c` device throws a clear domain error.
