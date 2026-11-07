:- module(core_tests, []).

:- use_module(library(array)).
:- use_module(library(clpBNR)).

:- begin_tests(core).

x(X) :- shape(X, [3]).
y(Y) :- shape(Y, [2, 3]).

test(transpose, [timeout(10), true(S == [3, 2])]) :-
   y(Y),
   over([I:3, J:2], [T[I, J] := Y[J, I]]),
   shape(T, S0),
   S0 = [3, 2],
   S = S0.
test(shape_is_a_lower_bound, [timeout(10), fail]) :-
   y(Y),
   over([I:3, J:2], [T[I, J] := Y[J, I]]),
   shape(T, [2, 2]).
test(matmul_two_boxes, [timeout(10), true(N == 2)]) :-
   shape(A, [2, 3]), shape(B, [3, 4]), shape(C, [2, 4]),
   over([I:2, J:4], [C[I, J] := 0]),
   over([I:2, J:4, K:3], [C[I, J] := C[I, J] + A[I, K] * B[K, J]]),
   get_attr(C, core, def(_, Boxes)),
   length(Boxes, N).
test(cumsum_extent_expression, [timeout(10), true(N == 5)]) :-
   shape(X, [N, 3]),
   over([J:3], [C[0, J] := X[0, J]]),
   over([T:N-1, J:3], [C[T+1, J] := C[T, J] + X[T+1, J]]),
   shape(C, [5, 3]),
   N = 5.
test(fibonacci_shifted_target, [timeout(10), fail]) :-
   over([], [F[0] := 1, F[1] := 1]),
   over([T:8], [F[T+2] := F[T] + F[T+1]]),
   shape(F, [9]).
test(rank_0_name, [timeout(10), true(S == [])]) :-
   x(X),
   over([], [Sum := 0]),
   over([K:3], [Sum := Sum + X[K]]),
   shape(Sum, S).
test(nested_box, [timeout(10), true(Ns == [1, 1])]) :-
   shape(F, [2, 2]), shape(X, [N, 2]),
   over([T:N-1], [over([I:2], [P[I] := 0]),
                  over([I:2, J:2], [P[I] := P[I] + F[I, J] * X[T, J]]),
                  over([I:2], [X[T+1, I] := P[I]])]),
   get_attr(P, core, def(_, Bp)), get_attr(X, core, def(_, Bx)),
   maplist(length, [Bp, Bx], Ns).
test(reads_relate_extents, [timeout(10), true(Lo == 3)]) :-
   shape(X, [N]),
   over([I:3], [_T[I] := X[I]]),
   range(N, [Lo, _]).
test(symbolic_constant, [timeout(10)]) :-
   shape(X, [N]),
   over([I:N], [_R[I] := X[N-1-I]]).
test(where_and_comparison, [timeout(10)]) :-
   x(X),
   over([I:3], [_R[I] := where(X[I] < 0, -X[I], X[I])]).

test(index_as_name, [timeout(10), throws(error(type_error(name, _), _))]) :-
   over([I:3], [I[0] := 1]).
test(name_as_index, [timeout(10), throws(error(type_error(axes, _), _))]) :-
   x(X),
   over([X:3], [_T[X] := 1]).
test(free_variable, [timeout(10), throws(error(type_error(index, _), _))]) :-
   x(X),
   over([I:3], [_T[I] := X[_]]).
test(undeclared_read, [timeout(10), throws(error(existence_error(name, _), _))]) :-
   over([I:3], [_T[I] := _X[I]]).
test(duplicate_axis, [timeout(10), throws(error(type_error(axes, _), _))]) :-
   over([I:3, I:2], [_T[I] := 1]).
test(inner_axis_shadows, [timeout(10), throws(error(type_error(axes, _), _))]) :-
   over([I:3], [over([I:2], [_T[I] := 1])]).
test(rank_mismatch, [timeout(10), throws(error(domain_error(rank(1), _), _))]) :-
   x(X),
   over([I:3, J:2], [_T[I, J] := X[I, J]]).
test(name_as_scalar, [timeout(10), throws(error(domain_error(rank(0), _), _))]) :-
   x(X),
   over([I:3], [_T[I] := X + 1]).
test(read_out_of_bounds, [timeout(10), throws(error(domain_error(in_bounds, _), _))]) :-
   x(X),
   over([I:3], [_T[I] := X[I+5]]).
test(write_out_of_bounds, [timeout(10), throws(error(domain_error(in_bounds, _), _))]) :-
   shape(T, [2]),
   over([I:3], [T[I] := 1]).
test(negative_subscript, [timeout(10), throws(error(domain_error(in_bounds, _), _))]) :-
   x(X),
   over([I:3], [_T[I] := X[2-I-1]]).
test(name_is_never_bound, [timeout(10), throws(error(permission_error(bind, name, _), _))]) :-
   x(X),
   X = foo.
test(not_a_shape, [timeout(10), throws(error(type_error(shape, _), _))]) :-
   shape(_, [2, foo]).
test(not_a_value, [timeout(10), throws(error(type_error(value, _), _))]) :-
   over([I:3], [_T[I] := foo(I)]).

% Kinds: inferred forwards from the values written, backwards from the uses of an input, and
% labelled once the program is built.
test(kind_float_accumulation, [timeout(10), true(K == float)]) :-
   x(X),
   over([I:3], [S[I] := 0]),
   over([I:3], [S[I] := S[I] + X[I]]),
   label_kinds([X, S]), kind(S, K).
test(kind_count_is_int, [timeout(10), true(K == int)]) :-
   x(X),
   over([I:3], [C[I] := 0]),
   over([I:3], [C[I] := C[I] + where(X[I] < 0, 1, 0)]),
   label_kinds([X, C]), kind(C, K).
test(kind_comparison_is_bool, [timeout(10), true(K == bool)]) :-
   x(X),
   over([I:3], [B[I] := X[I] < 0]),
   label_kinds([X, B]), kind(B, K).
test(kind_division_is_float, [timeout(10), true(K == float)]) :-
   over([I:3], [T[I] := I / 2]),
   label_kinds([T]), kind(T, K).
test(kind_index_arithmetic_is_int, [timeout(10), true(K == int)]) :-
   over([I:3], [T[I] := I + 1]),
   label_kinds([T]), kind(T, K).
test(kind_input_defaults_to_float, [timeout(10), true(K == float)]) :-
   x(X),
   over([I:3], [_T[I] := X[I]]),
   label_kinds([X]), kind(X, K).
test(kind_declared_before_shape, [timeout(10), true(K == int)]) :-
   kind(Idx, int), shape(Idx, [4]), elements(Idx, 0-2), shape(H, [3]),
   over([K4:4], [H[Idx[K4]] := 1]),
   label_kinds([Idx, H]), kind(Idx, K).
test(kind_where_condition_narrows_input, [timeout(10), true(K == bool)]) :-
   x(X),
   over([I:3], [_T[I] := where(X[I], 1, 0)]),
   label_kinds([X]), kind(X, K).
test(kind_subscript_defaults_to_int, [timeout(10), true(K == int)]) :-
   shape(Idx, [4]), elements(Idx, 0-2), shape(H, [3]),
   over([K4:4], [H[Idx[K4]] := 1]),
   label_kinds([Idx, H]), kind(Idx, K).
test(kind_float_subscript, [timeout(10), throws(error(domain_error(kind, _), _))]) :-
   shape(Idx, [4]), elements(Idx, 0-2), kind(Idx, float), shape(H, [3]),
   over([K4:4], [H[Idx[K4]] := 1]).
test(kind_where_condition_not_bool, [timeout(10), throws(error(domain_error(kind, _), _))]) :-
   x(X), kind(X, float),
   over([I:3], [_T[I] := where(X[I], 1, 0)]).
test(kind_declared_too_low, [timeout(10), throws(error(domain_error(kind, _), _))]) :-
   shape(S, [3]), kind(S, bool),
   over([I:3], [S[I] := 2]).
test(kind_unknown, [timeout(10), throws(error(type_error(oneof(_), _), _))]) :-
   x(X), kind(X, double).
test(kind_bits_is_int_of_anything, [timeout(10), true(K == int)]) :-
   x(X),
   over([I:3], [B[I] := bits(X[I])]),
   label_kinds([X, B]), kind(B, K).
test(permutation_is_int, [timeout(10), true(K == int)]) :-
   shape(P, [4]), permutation(P),
   label_kinds([P]), kind(P, K).
test(permutation_of_a_float, [timeout(10), throws(error(domain_error(kind, _), _))]) :-
   shape(P, [4]), kind(P, float), permutation(P).

% Beyond the structural check: a gather needs the range of the index array's elements, and
% a read of a place must come after its write.
test(gather, [timeout(10)]) :-
   shape(Idx, [4]), elements(Idx, 0-2), shape(H, [3]),
   over([K:4], [H[Idx[K]] := H[Idx[K]] + 1]).
test(gather_symbolic_range, [timeout(10), true(Lo == 3)]) :-
   shape(H, [N]), shape(Idx, [4]), elements(Idx, 0-(N-1)),
   over([K:4], [H[Idx[K]] := H[Idx[K]] + 1]),
   N = 3, range(N, [Lo, _]).
test(gather_range_above_extent, [timeout(10), throws(error(domain_error(in_bounds, _), _))]) :-
   shape(H, [N]), shape(Idx, [4]), elements(Idx, 0-N),
   over([K:4], [H[Idx[K]] := 1]).
test(gather_out_of_range, [timeout(10), throws(error(domain_error(in_bounds, _), _))]) :-
   shape(Idx, [4]), elements(Idx, 0-5), shape(H, [3]),
   over([K:4], [H[Idx[K]] := H[Idx[K]] + 1]).
test(gather_needs_a_range, [timeout(10), throws(error(existence_error(elements, _), _))]) :-
   shape(Idx, [4]), shape(H, [3]),
   over([K:4], [H[Idx[K]] := 1]).

% Beyond affine: a remainder is hulled by its operation on exact hulls of its operands, and the
% whole posted once as terms in the extents.
test(hull_mod_relates_extents, [timeout(10), true(Lo == 3)]) :-
   shape(X, [M]),
   over([I:7], [_T[I] := X[I mod 3]]),
   range(M, [Lo, _]).
test(hull_quotient_is_exact, [timeout(10), true(Lo == 4)]) :-
   shape(X, [M]),
   over([I:7], [_T[I] := X[I // 2]]),
   range(M, [Lo, _]).
test(hull_quotient_symbolic, [timeout(10)]) :-
   shape(X, [N]), shape(Y, [H]),
   over([I:N], [Y[I // 2] := X[I]]),
   N = 8, range(H, [4, _]).
test(hull_nested_affine_is_exact, [timeout(10), true(Lo == 13)]) :-
   shape(X, [M]),
   over([I:4, J:2], [_T[I, J] := X[(2*I + J) mod 7 + 2*I]]),
   range(M, [Lo, _]).
test(hull_clamp_fits_anything, [timeout(10)]) :-
   shape(X, [N]),
   over([I:N], [_T[I] := X[min(I*3, N-1)]]).
test(hull_where_is_the_union, [timeout(10), true(Lo == 7)]) :-
   shape(X, [M]),
   over([I:3], [_T[I] := X[where(I < 1, I + 4, I)]]),
   range(M, [Lo, _]).
test(hull_symbolic_coefficient, [timeout(10), true(Lo == 6)]) :-
   shape(X, [N, M]),
   over([I:2, J:3], [T[I*M + J] := X[I, J]]),
   N = 2, M = 3, shape(T, [L]), range(L, [Lo, _]).
test(hull_xor_with_a_power_of_two, [timeout(10)]) :-
   power_of_two(N), shape(X, [N]), shape(S, [P]), elements(S, 0-(N-1)),
   over([Pi:P, I:N], [_T[Pi, I] := X[I xor S[Pi]]]).
test(hull_xor_needs_a_power_of_two, [timeout(10), throws(error(domain_error(power_of_two, _), _))]) :-
   shape(X, [N]),
   over([I:N], [_T[I] := X[I xor 1]]).
test(hull_and_needs_no_declaration, [timeout(10)]) :-
   shape(X, [N]), shape(S, [P]), elements(S, 0-(N-1)),
   over([Pi:P, I:N], [_T[Pi, I] := X[I /\ S[Pi]]]).
test(hull_shift, [timeout(10), true(Lo == 2)]) :-
   shape(X, [M]),
   over([I:8], [_T[I] := X[I >> 2]]),
   range(M, [Lo, _]).
test(hull_rejects_a_float_subscript, [timeout(10), throws(error(domain_error(kind, _), _))]) :-
   shape(X, [4]),
   over([I:4], [_T[I] := X[I / 2]]).
test(hull_rejects_a_float_operand, [timeout(10), throws(error(domain_error(kind, _), _))]) :-
   shape(X, [4]), shape(W, [4]), kind(W, float),
   over([I:4], [_T[I] := X[W[I] mod 2]]).
test(hull_quotient_needs_a_positive_divisor, [timeout(10), throws(error(domain_error(positive, _), _))]) :-
   shape(X, [N]), shape(D, [1]), elements(D, 0-3),
   over([I:N], [_T[I] := X[I // D[0]]]).
test(power_of_two_on_a_number, [timeout(10)]) :-
   power_of_two(8).
test(power_of_two_rejects_six, [timeout(10), throws(error(domain_error(power_of_two, 6), _))]) :-
   power_of_two(6).
test(power_of_two_binds_to_a_power, [timeout(10)]) :-
   power_of_two(N), shape(_X, [N]), N = 512.
test(power_of_two_refuses_six_later, [timeout(10)]) :-
   power_of_two(N), shape(_X, [N]),
   \+ catch(N = 6, error(domain_error(power_of_two, _), _), fail).
test(read_before_write, [timeout(10), fixme(needs_dependence_analysis),
                         throws(error(domain_error(written, _), _))]) :-
   over([T:8], [F[T] := F[T+1]]).

:- end_tests(core).
