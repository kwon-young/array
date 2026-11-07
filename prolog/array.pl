:- module(array, []).

/** <module> Multidimensional arrays as boxes of equations, compiled to OpenCL

The user-facing predicates of the pack:

  - from array/core: the vocabulary of programs, over/2, shape/2, elements/2, kind/2,
    label_kinds/1, power_of_two/1, permutation/1, and the postfix operator [] of places;
  - from array/compile: program/2, eval/3, kernels/3, source/2, run/4, device_options/2;
  - from array/opencl: opencl_device/2, the devices a program runs on.

The modules under array/ export more, for tools and tests: load them by name.
*/

:- reexport(array/core).
:- reexport(array/compile, [program/2, eval/3, kernels/3, source/2, run/4, device_options/2]).
:- reexport(array/opencl, [opencl_device/2]).
