:- module(swipl_ld, [clang_format/2, compile_object/2, link_objects/2]).

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

compile_object(In, OutFile) :-
   tmp_file_stream(InFile, StreamIn, [extension(c)]),
   format(StreamIn, "~s", [In]),
   close(StreamIn),
   tmp_file_stream(OutFile, StreamOut, [extension(o)]),
   close(StreamOut),
   process_create(path('swipl-ld'), ['-fpic', '-cc-options,-march=native', '-O3', '-c', '-o', OutFile, InFile], [stdout(std), stderr(std)]).

link_objects(Objects, OutFile) :-
   tmp_file_stream(OutFile, StreamOut, [extension(so)]),
   close(StreamOut),
   append(['-fpic', '-march=native', '-O3', '-shared', '-o', OutFile], Objects, Options),
   process_create(path('swipl-ld'), Options, [stdout(std), stderr(std)]).
