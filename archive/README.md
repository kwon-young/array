# Archive

Earlier designs of the library, kept for reference.
None of it loads from here: the modules it used (`buffer`, `c99`, `gen_type`, `minimalloc`) have moved into the pack.
The tag `pre-core2-cleanup` is the last commit where the old design runs.

## The dict array (`array.pl`)

A NumPy-like lazy array as SWI-Prolog dicts, with views, fusion, a kernel IR and three runtimes.

- `array.pl`, `array_ref.pl`: the `array{}` dict, its ops and the `@=` scheduling.
- `view.pl`, `loop_index.pl`: zero-copy views, as clpfd relations.
- `dtype.pl`, `precision.pl`: storage types, value ranges and error bounds (clpBNR).
- `fusion.pl`: fusing the op graph into kernels.
- `ir*.pl`, `kernel_ir.md`: the kernel IR, its lowering, indexing and e-graph optimisation.
- `runtime_prolog.pl`, `runtime_c.pl`, `runtime_opencl.pl`, `kernel.pl`, `kernel_c.pl`, `swipl_ld.pl`: the backends.
- `lu_decomposition.pl`, `mem.pl`: LU solve and memory planning.
- `kalman.pl`: a Kalman filter example.
- `README.old.md`, `PLAN.md`: its README and cleanup plan.

## The `core` design

- `core.pl`, `core_array.pl`, `core_array.plt`, `core_tutorial.pl`: the step between the dict array and the boxes of the current design.

## Experiments

- `cparser.pl`: a C parser on `library(ffi)`.
- `promote_types.pl`, `generate_promote_types.py`: NumPy's type promotion table.
- `custom_constraints.pl`, `mem2.pl`, `test.pl`, `test_module.pl`, `kernel.c`, `mm.c`: spikes.
- `CONVENTIONS.md`: the conventions given to aider.
