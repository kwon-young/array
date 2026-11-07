:- module(array_ref, [array_ref/2]).

/** <module> References to arrays

A reference is a fresh variable naming an array through the attribute
array_ref. An array may then refer to itself, as an op reading what it
computes, without being a cyclic term: the link is in the attribute, which
no traversal of the term follows.
*/

% array_ref(?Ref, ?Array): Ref names Array. With Ref unbound and not yet a
% reference, Ref becomes one.
array_ref(Ref, Array), get_attr(Ref, array_ref, Array0) =>
   Array = Array0.
array_ref(Ref, Array), var(Ref) =>
   put_attr(Ref, array_ref, Array).

% A reference is never bound nor unified.
attr_unify_hook(_, _) :-
   fail.
