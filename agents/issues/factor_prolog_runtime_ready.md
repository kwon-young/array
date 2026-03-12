# Factor out remaining Prolog runtime code

**Priority**: High

## Description
To support modular runtimes (such as a future C or GPU backend), the `array.pl` core module must be completely backend-agnostic. Currently, `array.pl` contains hardcoded implementations for the `prolog` device. These must be moved to `runtime_prolog.pl` and accessed via standard dynamic dispatch (e.g., using `multifile` predicates).

## Acceptance Criteria
- [ ] `run_scheduleitem/2` clauses specific to the `prolog` device are moved from `array.pl` to `runtime_prolog.pl`.
- [ ] `dtype/3` clauses specific to the `prolog` device are moved from `array.pl` to `runtime_prolog.pl`.
- [ ] `broadcast_dtype/3` clauses specific to the `prolog` device are moved from `array.pl` to `runtime_prolog.pl`.
- [ ] `array.pl` defines these predicates as `multifile` (e.g., `:- multifile run_scheduleitem/2, dtype/3, broadcast_dtype/3.`) so other modules can extend them.
- [ ] Implementations in `runtime_prolog.pl` correctly attach to the multifile predicates defined in `array.pl` (e.g., by qualifying them like `array:dtype(prolog, 0, R) => R = boolean.`).
- [ ] All existing tests continue to pass without modification.

## Technical Notes
- The default device fallback in `M.default` (`option(device(Device), Merged, prolog)`) can remain in `array.pl` for ease of use.
- The forced conversion in `M.tolist()` (`M.contiguous().to(prolog).realize()`) is acceptable as it specifically converts internal data structures into a native Prolog list format.
- Make sure to review `runtime_prolog.pl` to see how it currently hooks into `array.pl` (e.g., it already extends `compile/2` via `array:M.compile(...)`) and follow the same conventions.
