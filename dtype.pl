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

% op_dtype(Op, Args, Result).
op_dtype(+, [boolean, boolean], boolean).
op_dtype(+, [int8, int8], int8).
