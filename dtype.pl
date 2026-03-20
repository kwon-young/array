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

:- module(dtype, [type_range/6]).

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

dtype_info(uint8, Var, Precision, Size) :-
   Var::integer,
   Size = 8,
   type_info(Var, Precision, Size, [signed(0)]).
dtype_info(uint16, Var, Precision, Size) :-
   Var::integer,
   Size = 16,
   type_info(Var, Precision, Size, [signed(0)]).
dtype_info(uint32, Var, Precision, Size) :-
   Var::integer,
   Size = 32,
   type_info(Var, Precision, Size, [signed(0)]).
dtype_info(uint64, Var, Precision, Size) :-
   Var::integer,
   Size = 64,
   type_info(Var, Precision, Size, [signed(0)]).

dtype_info(int8, Var, Precision, Size) :-
   Var::integer,
   Size = 8,
   type_info(Var, Precision, Size, [signed(1)]).
dtype_info(int16, Var, Precision, Size) :-
   Var::integer,
   Size = 16,
   type_info(Var, Precision, Size, [signed(1)]).
dtype_info(int32, Var, Precision, Size) :-
   Var::integer,
   Size = 32,
   type_info(Var, Precision, Size, [signed(1)]).
dtype_info(float32, Var, Precision, Size) :-
   Var::real,
   Size = 32,
   type_info(Var, Precision, Size, [exponent(8), mantissa(23), infinity(1)]).
dtype_info(int64, Var, Precision, Size) :-
   Var::integer,
   Size = 64,
   type_info(Var, Precision, Size, [signed(1)]).
type_info(Var, Precision, Size, Options) :-
   domain(Var, Domain),
   domain_info(Domain, Precision, Size, Options).
domain_info(boolean, 1, _, Options) :-
   option(min(0), Options, _),
   option(max(1), Options, _).
domain_info(integer(RMin, RMax), 1, Size, Options) :-
   option(min(Min), Options, _),
   option(max(Max), Options, _),
   option(signed(Signed), Options, _),
   Signed::boolean,
   integer_size(Size),
   signed_integer_range_size(SignedMin-SignedMax, Size),
   unsigned_integer_range_size(UnsignedMin-UnsignedMax, Size),
   {
      RMin =< RMax,
      (Signed and (Min == SignedMin) and (Max == SignedMax))
      or (~Signed and (Min == UnsignedMin) and (Max == UnsignedMax)),
      Min =< RMin, RMax =< Max
   }.
domain_info(float(RMin, RMax), Precision, Size, Options) :-
   option(min(Min), Options, _),
   option(max(Max), Options, _),
   option(exponent(E), Options, _),
   option(mantissa(M), Options, _),
   option(emax(EMax), Options, _),
   option(infinity(Infinity), Options, _),
   Infinity::boolean,
   Size::integer(8, 64),
   E::integer(4, 15),
   M::integer(2, 112),
   N::integer(3, 6),
   {  
      RMin =< RMax,
      Size is 2^N,
      Size is 1 + E + M,
      EMax is 2^(E - 1) - Infinity,
      Max is (2 - 2^(-M + 1 - Infinity)) * 2^EMax,
      Min is -Max,
      Min =< RMin, RMax =< Max,
      MaxRange is max(abs(RMin), abs(RMax)),
      MaxRange * 2^(-M) == PrecisionRange,
      PrecisionRange =< Precision
   }.
