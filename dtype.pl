% unified data type representation
% a data type is represented by a type (boolean, integer, float), a range and a size.
% type should always be bound
% range is a clpBNR variable and tracks the actual range of the array
% size is a clpBNR integer that can either be set by the user, or set by the device when compiling
% * for integer, device should always use the smallest integer size that can fit the given range
% * for float, fp32 should be the default size, as it is kind of the expected default precision for a float.
%   the user can set the size to constrain the possible precision:
%   * if the user specify size of 16 and the range is larger than fp16, the c device can use bf16 which has a larger range for less precision
%   * if the user specify size of 64 or 128, then the c device will use double or quad precision floats
%
% implicit broadcasting types can be declaratively, using clpfd constraints:
% * boolean -> integer -> float
% * range is tracked using clpBNR operation, although care must be taken to correctly model interval for float128 as it cannot be represented by a prolog float
%   * integer are clpBNR integer
%   * float are clpBNR real
% * size is a clpBNR integer, is the number of bits that will store the number and is linked to a maximum range that range cannot exceed

:- module(dtype, [dtype_info/3]).

:- use_module(library(clpBNR)).

integer_size(Size) :-
   N::integer(3, 6),
   Size::integer,
   { Size is 2^N }.
signed_integer_range_size(Min-Max, Size) :-
   {
      Max is 2^(Size - 1) - 1,
      Min is -(2^(Size - 1))
   }.
unsigned_integer_range_size(0-Max, Size) :-
   { Max is 2^Size - 1 }.

is_domain(Range, Domain) :-
   (  domain(Range, Domain)
   -> true
   ;  instantiation_error(Range::Domain)
   ).

dtype_info(bool, boolean(_, _), _Options) :-
   type_info(boolean, []).
dtype_info(uint8, integer(Min, Max), _Options) :-
   type_info(integer(Min, Max), [size(8), signed(0)]).
dtype_info(uint16, integer(Min, Max), _Options) :-
   type_info(integer(Min, Max), [size(16), signed(0)]).
dtype_info(uint32, integer(Min, Max), _Options) :-
   type_info(integer(Min, Max), [size(32), signed(0)]).
dtype_info(uint64, integer(Min, Max), _Options) :-
   type_info(integer(Min, Max), [size(64), signed(0)]).

dtype_info(int8, integer(Min, Max), _Options) :-
   type_info(integer(Min, Max), [size(8), signed(1)]).
dtype_info(int16, integer(Min, Max), _Options) :-
   type_info(integer(Min, Max), [size(16), signed(1)]).
dtype_info(int32, integer(Min, Max), _Options) :-
   type_info(integer(Min, Max), [size(32), signed(1)]).
dtype_info(int64, integer(Min, Max), _Options) :-
   type_info(integer(Min, Max), [size(64), signed(1)]).

dtype_info(float8_e4m3, real(Min, Max), Options) :-
   option(precision(Precision), Options, _),
   type_info(real(Min, Max), [size(8), precision(Precision), exponent(4),
                              mantissa(3), infinity(0)]).
dtype_info(float8_e5m2, real(Min, Max), Options) :-
   option(precision(Precision), Options, _),
   type_info(real(Min, Max), [size(8), precision(Precision), exponent(5),
                              mantissa(2), infinity(1)]).
dtype_info(bfloat16, real(Min, Max), Options) :-
   option(precision(Precision), Options, _),
   type_info(real(Min, Max), [size(16), precision(Precision), exponent(8),
                              mantissa(7), infinity(1)]).
dtype_info(float16, real(Min, Max), Options) :-
   option(precision(Precision), Options, _),
   type_info(real(Min, Max), [size(16), precision(Precision), exponent(5),
                              mantissa(10), infinity(1)]).
dtype_info(float32, real(Min, Max), Options) :-
   option(precision(Precision), Options, _),
   type_info(real(Min, Max), [size(32), precision(Precision), exponent(8),
                              mantissa(23), infinity(1)]).
dtype_info(float64, real(Min, Max), Options) :-
   option(precision(Precision), Options, _),
   type_info(real(Min, Max), [size(64), precision(Precision), exponent(11),
                              mantissa(52), infinity(1)]).
type_info(boolean, _).
type_info(integer(RMin, RMax), Options) :-
   option(size(Size), Options, _),
   option(signed(Signed), Options, _),
   Signed::boolean,
   integer_size(Size),
   signed_integer_range_size(SignedMin-SignedMax, Size),
   unsigned_integer_range_size(UnsignedMin-UnsignedMax, Size),
   {
      (Signed and (Min == SignedMin) and (Max == SignedMax))
      or (~Signed and (Min == UnsignedMin) and (Max == UnsignedMax)),
      Min =< RMin, RMax =< Max
   }.
type_info(real(RMin, RMax), Options) :-
   option(precision(Precision), Options, _),
   option(size(Size), Options, _),
   option(exponent(E), Options, _),
   option(mantissa(M), Options, _),
   option(emax(EMax), Options, _),
   option(infinity(Infinity), Options, _),
   Precision::real(0, inf),
   Infinity::boolean,
   Size::integer(8, 64),
   E::integer(4, 15),
   M::integer(2, 112),
   N::integer(3, 6),
   {  
      Size is 2^N,
      Size is 1 + E + M,
      EMax is 2^(E - 1) - Infinity,
      Max is (2 - 2^(-M + 1 - Infinity)) * 2^EMax,
      Min is -Max,
      Min =< RMin, RMax =< Max,
      MaxRange is max(abs(RMin), abs(RMax)),
      MaxRange * 2^(-M) =< Precision, Precision =< Max * 2^(-M)
   }.

type_min_max_range(boolean, Min, Max, Range) :-
   Range::boolean,
   { Min =< Range, Range =< Max }.
type_min_max_range(integer, Min, Max, Range) :-
   Range::integer(Min, Max).
type_min_max_range(float, Min, Max, Range) :-
   Range::real(Min, Max).

% Compile-time helpers for type promotion (approximating NumPy rules)
% dtype_rank(Type, Kind, Size).
% Kinds: 0 = bool, 1 = unsigned, 2 = signed, 3 = float
dtype_rank(bool, 0, 1).
dtype_rank(uint8, 1, 8).
dtype_rank(int8, 2, 8).
dtype_rank(uint16, 1, 16).
dtype_rank(int16, 2, 16).
dtype_rank(uint32, 1, 32).
dtype_rank(int32, 2, 32).
dtype_rank(uint64, 1, 64).
dtype_rank(int64, 2, 64).
dtype_rank(float8_e4m3, 3, 8).
dtype_rank(float8_e5m2, 3, 9).
dtype_rank(float16, 3, 16).
dtype_rank(bfloat16, 3, 17).
dtype_rank(float32, 3, 32).
dtype_rank(float64, 3, 64).

% 1. Same kind: Take the max of the widths.
promote_rule(K, S1, K, S2, K, S) :-
   S is max(S1, S2).

% 2. Different kind, different widths: Take max of widths and max of kinds.
promote_rule(K1, S1, K2, S2, K, S) :-
   dif(K1, K2),
   dif(S1, S2),
   K is max(K1, K2),
   S is max(S1, S2).

% 3. Different kind, same width: Multiply width by 2 (capped at 64), take max of kinds.
promote_rule(K1, S, K2, S, K, SOut) :-
   dif(K1, K2),
   K is max(K1, K2),
   SOut is min(64, S * 2).

numpy_promote(T1, T2, Promoted) :-
   dtype_rank(T1, K1, S1),
   dtype_rank(T2, K2, S2),
   promote_rule(K1, S1, K2, S2, K, S),
   dtype_rank(Promoted, K, S).

numpy_unary_float(T, float32) :-
   dtype_rank(T, Kind, _),
   Kind < 3.
numpy_unary_float(T, T) :-
   dtype_rank(T, Kind, _),
   Kind >= 3.

% Term expansion to generate all combinations as static facts
term_expansion(generate_op_dtypes, Clauses) :-
   DTypes = [bool, uint8, int8, uint16, int16, uint32, int32, uint64, int64, float8_e4m3, float8_e5m2, float16, bfloat16, float32, float64],
   
   findall(op_dtype(Op, [T1, T2], Res), (
      member(Op, [+, *]),
      member(T1, DTypes), member(T2, DTypes),
      numpy_promote(T1, T2, Res)
   ), BinMathClauses),
   
   findall(op_dtype(<, [T1, T2], bool), (
      member(T1, DTypes), member(T2, DTypes)
   ), CmpClauses),
   
   findall(op_dtype(Op, [T], Res), (
      member(Op, [sin, log, sqrt]),
      member(T, DTypes),
      numpy_unary_float(T, Res)
   ), UnaryClauses),
   
   append([BinMathClauses, CmpClauses, UnaryClauses], Clauses).

% Trigger the term expansion
generate_op_dtypes.
