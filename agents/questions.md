1. How should the generated C code be compiled and invoked from Prolog? Should it use SWI-Prolog's `ffi` pack, or generate a shared library to be loaded dynamically?
2. How will memory management be handled? (e.g., Will Prolog allocate the arrays and pass pointers, or will C handle allocation?)
3. Should the C runtime support all operations currently available in the Prolog runtime, or start with a specific subset?
4. Are there any specific compiler flags or C standards (e.g., C99, C11) required for the generated C code?
