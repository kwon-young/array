:- module(swipl_ld, [clang_format/2, compile_object/3, link_objects/2]).

:- use_module(library(process)).

do(StreamIn, In, StreamOut, Out) :-
   format(StreamIn, "~s", [In]),
   close(StreamIn),
   read_stream_to_codes(StreamOut, Out).

clang_format(In, Out) :-
   setup_call_cleanup(
      process_create(
         path('clang-format'),
         [],
         [stdin(pipe(StreamIn)), stdout(pipe(StreamOut))]),
      do(StreamIn, In, StreamOut, Out),
      (  close(StreamOut),
         (  is_stream(StreamIn)
         -> close(StreamIn)
         ;  true
         )
      )
   ).

% compile_object(+In, +Flags, -OutFile)
% OutFile is the object compiled from the C source In, with the compiler
% Flags.
compile_object(In, Flags, OutFile) :-
   tmp_file_stream(InFile, StreamIn, [extension(c)]),
   format(StreamIn, "~s", [In]),
   close(StreamIn),
   tmp_file_stream(OutFile, StreamOut, [extension(o)]),
   close(StreamOut),
   maplist([Flag, Option]>>atom_concat('-cc-options,', Flag, Option),
           Flags, Options),
   append([['-g', '-fpic', '-c'], Options, ['-o', OutFile, InFile]], Args),
   swipl_ld(Args).

link_objects(Objects, OutFile) :-
   tmp_file_stream(OutFile, StreamOut, [extension(so)]),
   close(StreamOut),
   append(['-g', '-fpic', '-shared', '-o', OutFile], Objects, Args),
   swipl_ld(Args).

% swipl-ld builds against the Prolog that runs it: its headers and library.
swipl_ld(Args) :-
   current_prolog_flag(executable, Prolog),
   process_create(path('swipl-ld'), ['-pl', Prolog | Args],
                  [stdout(std), stderr(std)]).
