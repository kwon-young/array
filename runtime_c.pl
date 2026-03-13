:- module(runtime_c, []).

:- use_module(array, []).
:- use_module(buffer).

% Compiles the operation for the given Array on the 'c' device.
array:M.compile(c, _Op) := _Dict :-
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
