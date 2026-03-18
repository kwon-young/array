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

:- use_module(library(clpBNR)).

integer_size(Size) :-
   N::integer(3, 6),
   { Size is 2^N }.
signed_integer_range_size(Min-Max, Size) :-
   {
      Max is 2^(Size - 1) - 1,
      Min is -(2^(Size - 1))
   }.
unsigned_integer_range_size(0-Max, Size) :-
   { Max is 2^Size - 1 }.

type_range_precision(boolean, Range, _) :-
   Range::boolean.
type_range(integer, Range, Options) :-
   option(size(Size), Options),
   option(signed(Signed), Options),
   option(min(Min), Options, _),
   option(max(Max), Options, _),
   integer_size(Size),
   (  domain(Range, integer(RMin, RMax))
   -> true
   ;  instantiation_error(Range)
   ),
   signed_integer_range_size(SignedMin-SignedMax, Size),
   unsigned_integer_range_size(UnsignedMin-UnsignedMax, Size),
   {
      Signed is (RMin < 0),
      (Signed and (Min == SignedMin) and (Max == SignedMax))
      or (~Signed and (Min == UnsignedMin) and (Max == UnsignedMax)),
      Min =< RMin, RMax =< Max
   },
   global_minimize(Size, Size).
type_range(float, Range, Options) :-
   option(size(Size), Options),
   option(precision(Precision), Options),
   E::integer(2, 15),
   M::integer(1, 112),
   option(exponent(E), Options, E),
   option(mantissa(M), Options, M),
   option(emax(EMax), Options, _),
   option(max(Max), Options, _),
   option(min(Min), Options, _),
   Infinity::boolean,
   option(infinity(Infinity), Options, Infinity),
   (  domain(Range, real(RMin, RMax))
   -> true
   ;  instantiation_error(Range)
   ),
   N::integer(3, 7),
   {  Size is 2^N,
      Size is 1 + E + M,
      EMax is 2^(E - 1) - Infinity,
      Max is (2 - 2^(-M)) * 2^EMax,
      Min is -Max,
      ((Min =< RMin) and (RMax =< Max)),
      MaxMag is max(abs(RMin), abs(RMax)),
      MaxMag * 2^(-M) =< Precision
   },
   global_minimize(Size, Size),
   enumerate([E, M]).
