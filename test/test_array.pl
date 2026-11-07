% The test suite of the array pack: every test/*.plt.
%
% swipl -g test_array -t halt test/test_array.pl         all the units
% swipl -g "test_array(compile_basics)" -t halt test/test_array.pl
% ctest --test-dir build --output-on-failure             after a cmake build
%
% The checkout's prolog/ and lib/<arch>/ come before any installed copy of the pack, so the
% suite tests the sources next to it; build the foreign libraries first (see README.md).

:- module(test_array, [test_array/0, test_array/1]).
:- use_module(library(plunit)).

:- multifile user:file_search_path/2.
:- dynamic user:file_search_path/2.

:- prolog_load_context(directory, Test),
   file_directory_name(Test, Root),
   directory_file_path(Root, prolog, Library),
   current_prolog_flag(arch, Arch),
   atomic_list_concat([Root, lib, Arch], /, Foreign),
   asserta(user:file_search_path(library, Library)),
   asserta(user:file_search_path(foreign, Foreign)).

:- prolog_load_context(directory, Test),
   directory_file_path(Test, '*.plt', Pattern),
   expand_file_name(Pattern, Files),
   load_files(Files, [if(not_loaded)]).

%! test_array is semidet.
%! test_array(+Spec) is semidet.
%
%  Run every unit, or the units and tests of Spec as run_tests/1 takes them; fail if a
%  test fails.
test_array :-
   run_tests.

test_array(Spec) :-
   run_tests(Spec).
