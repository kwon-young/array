# Array.pl

This library aims to bring strided array to prolog.
It is basically a numpy clone but fully implemented in prolog.

In addition to the numpy design, it also aims to be fully lazy, meaning that `A + B` only schedule an operation, and is only called when needed.
Furthermore, it also aims to be extensible in terms of backend (or device) and types.
Out of the box, I would like to support normal prolog arithmetic and clpBNR, and ultimately have a C backend which would generate specialized kernel on the fly (and even further, an openCL backend for parallel computing and GPUs).
