:- module(runtime_c, []).

:- use_module(array, []).
:- use_module(buffer).

% Compiles the operation for the given Array on the 'c' device.
array:M.compile(c, true) := _Dict :-
   throw(not_implemented).
array:M.compile(c, view(_)) := _Dict :-
   throw(not_implemented).
array:M.compile(c, constant(_)) := _Dict :-
   throw(not_implemented).
array:M.compile(c, solve(A, B)) := _Dict :-
   throw(not_implemented).
array:M.compile(c, rand) := Dict :-
   Dict = M.compile(c, elementwise(random_float)).
array:M.compile(c, contiguous(Parent)) := Dict :-
   Dict = M.compile(c, elementwise(contiguous(Parent))).
array:M.compile(c, A<B) := Dict :-
   Dict = M.compile(c, elementwise(A<B)).
array:M.compile(c, A+B) := Dict :-
   Dict = M.compile(c, elementwise(A+B)).
array:M.compile(c, A*B) := Dict :-
   Dict = M.compile(c, elementwise(A*B)).
array:M.compile(c, sin(A)) := Dict :-
   Dict = M.compile(c, elementwise(sin(A))).
array:M.compile(c, log(A)) := Dict :-
   Dict = M.compile(c, elementwise(log(A))).
array:M.compile(c, sqrt(A)) := Dict :-
   Dict = M.compile(c, elementwise(sqrt(A))).
array:M.compile(c, elementwise(Op)) := _Dict :-
   throw(not_implemented).
array:M.compile(c, reduce(Op, Axes, Parent)) := _Dict :-
   throw(not_implemented).

% Allocates the physical memory or underlying data storage for Array on the 'c' device.
array:allocate(c, M) :-
    buffer_alloc(M.data, M.dtype, M.size(), true).

% Maps a Prolog Value to its corresponding data type representation supported by the 'c' device.
array:dtype(c, _Value, _DType) :-
    throw(not_implemented).

% Defines the type promotion rules on the 'c' device.
array:broadcast_dtype(c, _DType1, _DType2) :-
    throw(not_implemented).
