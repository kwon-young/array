:- module(ir_c, [ir_c/3]).

/** <module> The C dialects of the kernel IR

Prints a kernel clause of the IR as the body of a C or OpenCL C function
computing one element of the output: its index is the output forall's
domain.
*/

:- use_module(library(apply)).
:- use_module(library(lists)).
:- use_module(library(pairs)).
:- use_module(c99).
:- use_module(ir, [ir_formats/2]).
:- use_module(kernel_c, [type_name/3, lowest/3, reduction_hint/4, loops/5,
                         c_condition/2, numlist_/2]).

% ir_c(+Dialect, +Kernel, -Code)
% Code is c_kernel(Buffers, Shape, Index, Body):
%   * Buffers are the buffer parameters, Format:Name with a0 the output;
%   * Shape is the output's shape, and Index its index parameters, int:i1...;
%   * Body are the statements computing the element at Index.
% Value variables stay Prolog variables, to be named when printed.
ir_c(Dialect, Kernel0, Code) :-
   copy_term(Kernel0, Kernel),
   ir_formats(Kernel, Formats),
   Kernel = (Head :- forall(Domain, Element)),
   Head =.. [_ | Buffers],
   length(Buffers, NBuffers),
   N is NBuffers - 1,
   numlist(0, N, Numbers),
   maplist(buffer_name, Buffers, Numbers, Names, BufferFormats),
   pairs_keys_values(Params, BufferFormats, Names),
   conjunction_list(Domain, Binders),
   length(Binders, NIndex),
   numlist_(NIndex, IndexNumbers),
   maplist(index_param, Binders, IndexNumbers, Shape, Index),
   Ctx = ctx{dialect: Dialect, formats: Formats, declared: []},
   phrase(statements(Element, Ctx), Statements),
   foldl(conjoin, Statements, true, Body),
   Code = c_kernel(Params, Shape, Index, Body).

% A buffer is named aN, and the variable naming it in the IR becomes that
% name.
buffer_name(Buffer-Format, N, Name, Format) :-
   atom_concat(a, N, Name),
   Buffer = Name.

% The output's index variables become the parameters i1, i2...
index_param(between(0, Max, I), K, Dim, int:I) :-
   Dim is Max + 1,
   atom_concat(i, K, I).

loop_index(between(0, Max, J), Dim, int:J) :-
   Dim is Max + 1.

conjoin(Goal, Conjunction0, Conjunction) :-
   mkconj(Conjunction0, Goal, Conjunction).

binder(between(_, _, _)).

conjunction_list(true, List) =>
   List = [].
conjunction_list((A, B), List) =>
   conjunction_list(A, LA),
   conjunction_list(B, LB),
   append(LA, LB, List).
conjunction_list(Goal, List) =>
   List = [Goal].

% Statements
% ==========

% statements(+Goal, +Ctx)//
statements((A, B), Ctx) ==>
   statements(A, Ctx),
   statements(B, Ctx).
statements(true, _) ==>
   [].
statements(simd(Goal), Ctx) ==>
   statements(Goal, Ctx).
statements(parallel(Goal), Ctx) ==>
   statements(Goal, Ctx).
statements(load(Buffer-_, Index, Value), Ctx) ==>
   assign(Value, Buffer[Index], Ctx).
statements(Value is Expr, Ctx) ==>
   { expr(Expr, Ctx, CExpr) },
   assign(Value, CExpr, Ctx).
statements(cast(Format, In, Out), Ctx) ==>
   { cast_expr(Format, In, Ctx, CExpr) },
   assign(Out, CExpr, Ctx).
statements(store(Buffer-_, Index, Expr), Ctx) ==>
   { expr(Expr, Ctx, CExpr) },
   [Buffer[Index] = CExpr].
% a comparison's value
statements((Cond -> Value = 1 ; Value = 0), Ctx) ==>
   { condition(Cond, Ctx, CCond) },
   assign(Value, CCond, Ctx).
statements((Cond -> Then ; Else), Ctx) ==>
   { both_assigned(Then, Else, Shared) },
   declarations(Shared, Ctx),
   {  condition(Cond, Ctx, CCond),
      append(Shared, Ctx.declared, Declared),
      BranchCtx = Ctx.put(declared, Declared),
      block(Then, BranchCtx, CThen),
      block(Else, BranchCtx, CElse)
   },
   if_statement(CCond, CThen, CElse).
statements(Value = Number, Ctx), number(Number) ==>
   assign(Value, Number, Ctx).
statements(aggregate_all(Aggregate, Goal, Result), Ctx) ==>
   reduction(Aggregate, Goal, Result, Ctx).

block(Goal, Ctx, Block) :-
   phrase(statements(Goal, Ctx), Statements),
   foldl(conjoin, Statements, true, Block).

if_statement(Cond, Then, true) ==>
   [if Cond { Then }].
if_statement(Cond, Then, Else) ==>
   [if_else(Cond, Then, Else)].

% assign(+Var, +CExpr, +Ctx)//: a declaration, unless Var was declared before
% a conditional assigning it.
assign(Var, CExpr, Ctx), declared(Var, Ctx) ==>
   [Var = CExpr].
assign(Var, CExpr, Ctx) ==>
   { var_type(Var, Ctx, Type) },
   [Type:Var = CExpr].

declarations([], _) ==>
   [].
declarations([Var | Vars], Ctx) ==>
   { var_type(Var, Ctx, Type) },
   [Type:Var],
   declarations(Vars, Ctx).

declared(Var, Ctx) :-
   member(V, Ctx.declared),
   V == Var,
   !.

var_type(Var, Ctx, Type) :-
   var_format(Var, Ctx, Format),
   type_name(Ctx.dialect, Format, Type).

var_format(Var, Ctx, Format) :-
   member(V-Format, Ctx.formats),
   V == Var,
   !.

% The values both branches of a conditional assign: they are declared
% before it.
both_assigned(Then, Else, Shared) :-
   phrase(assigned(Then), ThenVars),
   phrase(assigned(Else), ElseVars),
   include(member_eq(ElseVars), ThenVars, Shared).

member_eq(Vars, Var) :-
   member(V, Vars),
   V == Var,
   !.

assigned((A, B)) ==>
   assigned(A),
   assigned(B).
assigned(load(_, _, V)) ==>
   [V].
assigned(V is _) ==>
   [V].
assigned(cast(_, _, V)) ==>
   [V].
assigned(V = N), number(N) ==>
   [V].
assigned(aggregate_all(_, _, V)) ==>
   [V].
assigned(_) ==>
   [].

% A reduction accumulates in its result's format, over a loop per binder.
reduction(Aggregate, Goal, Result, Ctx) -->
   {  Aggregate =.. [Op, Template],
      conjunction_list(Goal, Goals),
      partition(binder, Goals, Binders, Body0),
      maplist(loop_index, Binders, Dims, TypedJs),
      var_format(Result, Ctx, Format),
      type_name(Ctx.dialect, Format, Type),
      identity(Op, Ctx.dialect, Format, Identity),
      foldl(conjoin, Body0, true, BodyGoal),
      phrase(statements(BodyGoal, Ctx), Statements0),
      expr(Template, Ctx, Item0),
      update(Op, Result, Type, Item0, Update),
      append(Statements0, Update, Statements),
      foldl(conjoin, Statements, true, LoopBody),
      reduction_op(Op, ReductionOp),
      reduction_hint(Ctx.dialect, ReductionOp, Result, Hint),
      loops(Dims, TypedJs, LoopBody, Hint, Loop)
   },
   [Type:Result = Identity, Loop].

identity(sum, _, _, Identity) =>
   Identity = 0.
identity(max, Dialect, Format, Identity) =>
   lowest(Dialect, Format, Identity).

reduction_op(sum, Op) => Op = (+).
reduction_op(max, Op) => Op = (<).

% A maximum propagates NaN, as aggregate_all/3 does: once Acc is NaN,
% Acc < Item is always false.
update(sum, Acc, _, Item, Update) =>
   Update = [Acc = Acc + Item].
update(max, Acc, Type, Item0, Update) =>
   Update = [Type:Item = Item0,
             if(or(Acc < Item, Item =\= Item)) { Acc = Item }].

% Expressions
% ===========

% A value or index expression of the IR, as a C expression.
expr(Var, _, C), var(Var) =>
   C = Var.
expr(Atom, _, C), atom(Atom), Atom \== random_float =>
   C = Atom.
expr(Number, _, C), number(Number) =>
   C = Number.
expr(random_float, _, C) =>
   C = cast(rand(), double) / 'RAND_MAX'.
expr(Expr, Ctx, C), compound(Expr) =>
   compound_name_arguments(Expr, Name, Args),
   maplist(expr_of(Ctx), Args, CArgs),
   compound_name_arguments(C, Name, CArgs).

expr_of(Ctx, Expr, C) :-
   expr(Expr, Ctx, C).

% A cast rounds like Prolog integer/1 from a float to an integer format,
% instead of truncating like C.
cast_expr(Format, In, Ctx, CExpr) :-
   type_name(Ctx.dialect, Format, Type),
   expr(In, Ctx, CIn),
   (  float_expression(In, Ctx),
      \+ float_format(Format)
   -> CExpr = cast(round(CIn), Type)
   ;  CExpr = cast(CIn, Type)
   ).

float_expression(Number, _), float(Number) =>
   true.
float_expression(Number, _), integer(Number) =>
   fail.
float_expression(random_float, _) =>
   true.
float_expression(Var, Ctx), var(Var) =>
   var_format(Var, Ctx, Format),
   float_format(Format).
float_expression(Expr, Ctx), compound(Expr) =>
   compound_name_arguments(Expr, _, Args),
   member(A, Args),
   float_expression(A, Ctx),
   !.

float_format(float16).
float_format(float32).
float_format(float64).

condition(Cond, Ctx, CCond) :-
   expr_condition(Cond, Ctx, Cond1),
   c_condition(Cond1, CCond).

expr_condition((A, B), Ctx, C) =>
   expr_condition(A, Ctx, CA),
   expr_condition(B, Ctx, CB),
   C = (CA, CB).
expr_condition(Comparison, Ctx, C) =>
   expr(Comparison, Ctx, C).
