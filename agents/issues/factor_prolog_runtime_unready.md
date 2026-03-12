Priority: High

# Factor out remaining Prolog runtime code

The prolog runtime specific code needs to be fully factored out to support modular runtimes.
Currently, `array.pl` contains hardcoded references to the `prolog` device, such as in `run_scheduleitem/2`, `dtype/3`, and `broadcast_dtype/3`.
These need to be moved to `runtime_prolog.pl` or properly abstracted to allow seamless dynamic dispatch for additional runtimes.
