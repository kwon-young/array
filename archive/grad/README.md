# grad2: an autograd prototype

`grad2.pl` differentiates the boxes of core2 as source: `vjp/4` and `grad/3` in reverse mode, `jvp/5` in forward mode, `partial/3` for one equation.
`grad2.plt` is its suite.
Both predate the pack layout: they load `core2` and `compile2`, now `library(array/core)` and `library(array/compile)`.
Open questions when it was set aside: in-place values (names written more than once), and plans with several outputs.

`compile2-epilogue-overwrites.diff` is a fix found alongside it, against `compile2.pl`/`compile2.plt` before the move to `prolog/array/compile.pl` and `test/compile.plt`:
an epilogue that adds into a name written before it, `Y[Ts] := Y[Ts] + C[Ts]`, must load that name's register tile instead of only storing it.
