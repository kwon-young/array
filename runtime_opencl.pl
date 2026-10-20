:- module(runtime_opencl, []).

/** <module> OpenCL device

An array on the device opencl(Name) lives in a buffer of the OpenCL device
named Name (see opencl:opencl_device/2), such as opencl(pocl) or
opencl(nvidia).

It exchanges data with the C device only: a transfer is a byte copy between
an OpenCL buffer and a C buffer of the same format, so it is exact.
Prolog data goes through the C device.
*/

:- use_module(array, []).
:- use_module(buffer).
:- use_module(opencl).

% Devices
% =======

% device_state(Name, Device, Context, Queue): a device is set up on its first
% use, and kept for the session.
:- dynamic device_state/4.

device(Name, Device, Context, Queue), device_state(Name, Device0, Context0, Queue0) =>
   Device = Device0,
   Context = Context0,
   Queue = Queue0.
device(Name, Device, Context, Queue), opencl_device(Name, Device0) =>
   cl_context(Device0, Context0),
   cl_queue(Context0, Device0, false, Queue0),
   assertz(device_state(Name, Device0, Context0, Queue0)),
   Device = Device0,
   Context = Context0,
   Queue = Queue0.
device(Name, _, _, _) =>
   existence_error(opencl_device, Name).

% A device stores the formats of the C device, except float16 and float64
% without their extension.
supported_format(Device, float16) =>
   extension(Device, "cl_khr_fp16").
supported_format(Device, float64) =>
   extension(Device, "cl_khr_fp64").
supported_format(_, _) =>
   true.

extension(Device, Extension) :-
   cl_device_info(Device, extensions, Extensions),
   split_string(Extensions, " ", " ", Names),
   memberchk(Extension, Names).

% Formats
% =======

array:default_format(opencl(_), M, Format) :-
   array:default_format(c, M, Format).
array:float_formats(opencl(Name), Formats) :-
   opencl_device(Name, Device),
   array:float_formats(c, CFormats),
   include(supported_format(Device), CFormats, Formats).
array:M.dtype_size(opencl(_)) := Size :-
   buffer_type_size(M.dtype(), Size).

% Buffers
% =======

array:allocate(opencl(Name), M) :-
   device(Name, _, Context, Queue),
   Bytes is M.datasize * M.dtype_size(),
   buffer(Context, Bytes, M.data),
   cl_fill(Queue, M.data, Bytes, [], Filled),
   cl_wait([Filled]).

% Transfers
% =========

array:M.to(c, opencl(Name)) := Dict :-
   M1 = M.contiguous().realize(),
   device(Name, Device, Context, Queue),
   Format = M1.dtype(),
   check_format(Name, Device, Format),
   bytes(M1, Offset, Bytes),
   buffer_offset(M1.data, Format, M1.datasize, 0, Pointer0),
   Pointer is Pointer0 + Offset,
   buffer(Context, Bytes, Mem),
   copy(cl_write, Queue, Mem, 0, Pointer, Bytes),
   Dict = M.empty(M1.shape(), [device(opencl(Name)), data(Mem), format(Format),
                               precision(M1.precision)]).

array:M.to(opencl(Name), c) := Dict :-
   M1 = M.contiguous().realize(),
   device(Name, _, _, Queue),
   Format = M1.dtype(),
   Size = M1.size(),
   bytes(M1, Offset, Bytes),
   buffer_alloc(Buffer, Format, Size, false),
   buffer_offset(Buffer, Format, Size, 0, Pointer),
   copy(cl_read, Queue, M1.data, Offset, Pointer, Bytes),
   Dict = M.empty(M1.shape(), [device(c), data(Buffer), format(Format),
                               precision(M1.precision)]).

% Prolog and OpenCL exchange data through the C device.
array:M.to(prolog, opencl(Name)) := Dict :-
   Dict = M.to(c).to(opencl(Name)).
array:M.to(opencl(_Name), prolog) := Dict :-
   Dict = M.to(c).to(prolog).

check_format(_, Device, Format), supported_format(Device, Format) =>
   true.
check_format(Name, _, Format) =>
   throw(error(unsupported_format(opencl(Name), Format), _)).

% The elements of a contiguous array are the Bytes from Offset in its buffer.
bytes(M, Offset, Bytes) :-
   Size = M.dtype_size(),
   Offset is M.view().offset * Size,
   Bytes is M.size() * Size.

% OpenCL has no empty buffer.
buffer(Context, Bytes, Mem) :-
   Size is max(1, Bytes),
   cl_buffer(Context, Size, Mem).

% OpenCL has no empty copy.
copy(_, _, _, _, _, 0) =>
   true.
copy(Copy, Queue, Mem, Offset, Pointer, Bytes) =>
   call(Copy, Queue, Mem, Offset, Pointer, Bytes).

:- multifile prolog:error_message//1.

prolog:error_message(unsupported_format(Device, Format)) -->
   [ 'The device ~w has no ~w format'-[Device, Format] ].

:- begin_tests(opencl_device).

:- use_module(array).

% A C array of Values in Format.
c_array(Values, Kind, Format, A) :-
   length(Values, N),
   Data =.. [data | Values],
   buffer_from_data(Buffer, Format, N, Data),
   A = array{}.empty([N], [device(c), dtype(Kind), data(Buffer),
                           format(Format)]).

c_values(int8, integer, [-128, 0, 127]).
c_values(uint8, integer, [0, 1, 255]).
c_values(int16, integer, [-32768, 7, 32767]).
c_values(uint16, integer, [0, 7, 65535]).
c_values(int32, integer, [-2147483648, 7, 2147483647]).
c_values(uint32, integer, [0, 7, 4294967295]).
c_values(int64, integer, [-9223372036854775808, 7, 9223372036854775807]).
c_values(uint64, integer, [0, 7, 18446744073709551615]).
c_values(bool, boolean, [0, 1, 1]).
c_values(float32, float, [1.5, -0.25, 1024.0]).
c_values(float64, float, [1.5, -0.1, 1.0e300]).

device_format(Name, Format, Kind, Values) :-
   opencl_device(Name, Device),
   c_values(Format, Kind, Values),
   supported_format(Device, Format).

test('c round trip keeps the format and the values',
     [forall(device_format(Name, Format, Kind, Values))]) :-
   c_array(Values, Kind, Format, A),
   B = A.to(opencl(Name)),
   B.dtype() == Format,
   C = B.to(c),
   C.dtype() == Format,
   C.tolist() == Values.

test('prolog round trip', [forall(opencl_device(Name, _))]) :-
   forall(member(L, [[1, -2, 300], [[1.5, -2.25], [0.5, 4.0]], [0, 1, 1]]),
          (  A = array{}.fromlist(L, [device(opencl(Name))]),
             A.device == opencl(Name),
             A.tolist() == L
          )).

test('allocation is zeroed', [forall(opencl_device(Name, _))]) :-
   A = array{}.empty([3], [device(opencl(Name)), dtype(integer),
                           format(int32)]),
   array:allocate(A.device, A),
   A.tolist() == [0, 0, 0].

test('a format without its extension fails loudly',
     [forall((opencl_device(Name, Device), \+ supported_format(Device, float16)))]) :-
   c_array([1.5], float, float16, A),
   catch(_ = A.to(opencl(Name)), error(E, _), true),
   E == unsupported_format(opencl(Name), float16).

test('an unknown device fails loudly',
     [throws(error(existence_error(opencl_device, nowhere), _))]) :-
   _ = array{}.fromlist([1], [device(opencl(nowhere))]).

:- end_tests(opencl_device).
