:- use_module(library(clpfd)).

:- multifile clpfd:run_propagator/2.

mymin(Min, Var) :-
   clpfd:make_propagator(mymin(Min, Var), Prop),
   clpfd:init_propagator(Var, Prop),
   clpfd:trigger_once(Prop).

clpfd:run_propagator(mymin(Min, Var), MState) :-
   (  ground(Var)
   -> clpfd:kill(MState)
   ;  Min #=< Var
   ).
