:- module(runtime_prolog, []).

:- use_module(array, []).
:- use_module(lu_decomposition).
:- use_module(ir_lower, [lower_kernel/5]).
:- use_module(ir_prolog, [ir_prolog/2]).

/* 
 * Runtime Backend Interface
 * =========================
 * To be used by array.pl, a runtime backend (device) must implement the
 * following multifile predicates in the `array` module:
 *
 * - array:compile(Device, Op, Array, CompiledDict)
 *   (Often implemented via dict method: array:Array.compile(Device, Op) := CompiledDict)
 *   Compiles the operation `Op` for the given `Array` on `Device`. 
 *   Returns a new dict containing at least a `kernel` key with a callable goal 
 *   that performs the operation.
 *
 * - array:allocate(Device, Array)
 *   Allocates the physical memory or underlying data storage for `Array` on `Device`.
 *   Typically binds the `data` field of the Array dict.
 *
 * - array:dtype(Device, Value, DType)
 *   Maps a Prolog `Value` to its corresponding data type representation (e.g., 
 *   boolean, integer, float) supported by the backend on `Device`.
 *
 * - array:broadcast_dtype(Device, DType1, DType2)
 *   Defines the type promotion rules. It should succeed if `DType1` can be 
 *   safely broadcast/promoted to `DType2` on the given `Device`.
 */

array:_M.dtype_size(prolog) := 1 :-
   true.

% Prolog floats are doubles; integers and booleans are exact.
array:default_format(prolog, M, Format) :-
   prolog_format(M.dtype, Format).

prolog_format(float, Format) =>
   Format = float64.
prolog_format(Kind, Format) =>
   Format = Kind.

array:float_formats(prolog, [float64]).

% Ops a Prolog kernel computes from its inputs.
array:expression_op(prolog, _+_).
array:expression_op(prolog, _*_).
array:expression_op(prolog, _<_).
array:expression_op(prolog, sin(_)).
array:expression_op(prolog, log(_)).
array:expression_op(prolog, sqrt(_)).
array:expression_op(prolog, float(_)).
array:expression_op(prolog, integer(_)).
array:expression_op(prolog, reduce(_, _, _)).
array:compute_format(prolog, _, float64).

array:M.compile(prolog, true) := Dict :-
   Dict = M.put(kernel, true).
array:M.compile(prolog, view(_)) := Dict :-
   Dict = M.put(kernel, true).
array:M.compile(prolog, constant(_)) := Dict :-
   Dict = M.put(kernel, true).
array:M.compile(prolog, solve(A, B)) := Dict :-
    [N, N] = A.shape(),
    (  B.shape() = [N, M_]
    -> true
    ;  B.shape() = [N], M_ = 1
    ),
    OffsetA = A.view().offset,
    OffsetB = B.view().offset,
    OffsetX = M.view().offset,
    Dict = M.put(kernel,
                 lu_decomposition:solve(A.data, OffsetA,
                                        B.data, OffsetB,
                                        N, M_, M.data, OffsetX)).
array:M.compile(prolog, Op) := Dict :-
   compile_kernel(M, Op, Dict).

% compile_kernel(+M, +Op, -Dict)
% Dict is M with a kernel computing Op into M: the kernel IR of Op, in its
% Prolog dialect, as a clause of the kernel module.
compile_kernel(M, Op, Dict) :-
   lower_kernel(prolog, M, Op, Kernel, Arrays),
   ir_prolog(Kernel, (Head0 :- Body)),
   Head0 =.. [_ | Params],
   % A kernel is named after its code, so a kernel already defined is reused.
   variant_sha1(Params-Body, KernelId),
   Head =.. [KernelId | Params],
   define_kernel(Head, Body),
   maplist(get_dict(data), Arrays, Datas),
   Call =.. [KernelId | Datas],
   Dict = M.put(kernel, kernel:Call).

define_kernel(Head, _), functor(Head, Name, Arity),
      current_predicate(kernel:Name/Arity) =>
   true.
define_kernel(Head, Body) =>
   assertz((kernel:Head :- Body)).

array:allocate(prolog, M) :-
   compound_name_arity(M.data, data, M.datasize).

% DTypes
% ======
% array:dtype(prolog, 0, R) => R = boolean.
% array:dtype(prolog, 1, R) => R = boolean.
% array:dtype(prolog, X, R), float(X) => R = float.
% array:dtype(prolog, X, R), integer(X) => R = integer.
% array:dtype(prolog, X, R), rational(X) => R = rational.
% array:dtype(prolog, X, DType), var(X) => when(ground(X), array:dtype(prolog, X, DType)).
%
% array:broadcast_dtype(prolog, boolean, integer).
% array:broadcast_dtype(prolog, integer, rational).
% array:broadcast_dtype(prolog, rational, float).
