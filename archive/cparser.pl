:- use_module(library(dcg/basics)).
:- use_module(library(dcg/high_order)).
:- use_module(library(ffi)).

translation_unit(ExternalDecl) -->
   sequence(external_decl, ExternalDecl).

external_decl(Decl) -->
   function_definition(Decl).
external_decl(decl(DeclSpec, InitDeclaratorList)) -->
   decl(DeclSpec, InitDeclaratorList).

function_definition(a(DeclSpecs, Declarator, CompoundStat)) -->
   decl_specs(DeclSpecs), declarator(Declarator), compound_stat(CompoundStat).

decl(DeclSpecs, InitDeclaratorList) -->
   decl_specs(DeclSpecs), " ", sequence(init_declarator, InitDeclaratorList), ";".
decl(DeclSpecs) -->
   decl_specs(DeclSpecs).

decl_specs(storage_class_spec(StorageClassSpec, DeclSpecs)) -->
   storage_class_spec(StorageClassSpec), decl_specs(DeclSpecs).
decl_specs(storage_class_spec(StorageClassSpec)) -->
   storage_class_spec(StorageClassSpec).
decl_specs(type_spec(TypeSpec, DeclSpecs)) -->
   type_spec(TypeSpec), decl_specs(DeclSpecs).
decl_specs(type_spec(TypeSpec)) -->
   type_spec(TypeSpec).
decl_specs(type_qualifier(TypeQualifier, DeclSpecs)) -->
   type_qualifier(TypeQualifier), decl_specs(DeclSpecs).
decl_specs(type_qualifier(TypeQualifier)) -->
   type_qualifier(TypeQualifier).

storage_class_spec(auto) -->
   "auto".
storage_class_spec(register) -->
   "register".
storage_class_spec(static) -->
   "static".
storage_class_spec(extern) -->
   "extern".
storage_class_spec(typedef) -->
   "typedef".

type_spec(void) -->
   "void".
type_spec(char) -->
   "char".
type_spec(short) -->
   "short".
type_spec(int) -->
   "int".
type_spec(long) -->
   "long".
type_spec(float) -->
   "double".
type_spec(signed) -->
   "signed".
type_spec(unsigned) -->
   "unsigned".
type_spec(type_spec(integer, Signed, Size)) -->
   { integer_size(Size) },
   signed(Signed), "int", integer(Size), "_t".
type_spec(type_spec(float, true, Size)) -->
   { float_size(Size) },
   "_Float", integer(Size).
integer_size(8).
integer_size(16).
integer_size(32).
integer_size(64).
float_size(16).
float_size(32).
float_size(64).
float_size(128).
signed(true) -->
   [].
signed(false) -->
   "u".

type_qualifier(const) -->
   "const".
type_qualifier(volatile) -->
   "volatile".

spec_qualifier(type_spec(TypeSpec)) -->
   type_spec(TypeSpec).
spec_qualifier(type_qualifier(TypeQualifier)) -->
   type_qualifier(TypeQualifier).

init_declarator(init_declarator(Declarator)) -->
   declarator(Declarator).
init_declarator(init_declarator(Declarator, Initializer)) -->
   declarator(Declarator), "=", initializer(Initializer).

declarator(declarator(Pointer, DirectDeclarator)) -->
   pointer(Pointer), direct_declarator(DirectDeclarator).
declarator(declarator(DirectDeclarator)) -->
   direct_declarator(DirectDeclarator).

id(Id) -->
   csym(Id), !.
direct_declarator(id(Id)) -->
   id(Id).
direct_declarator('()'(Declarator)) -->
   "(", declarator(Declarator), ")".
direct_declarator(DirectDeclarator[ConstExp]) -->
   direct_declarator(DirectDeclarator), "[", const_exp(ConstExp), "]".
direct_declarator(DirectDeclarator[]) -->
   direct_declarator(DirectDeclarator), "[]".

pointer(pointer(TypeQualifierList)) -->
   "*", sequence(type_qualifier, TypeQualifierList).
pointer(pointer(TypeQualifierList, Pointer)) -->
   "*", sequence(type_qualifier, TypeQualifierList), pointer(Pointer).

param_type_list(param_type_list(ParamList)) -->
   sequence(param_decl, ",", ParamList).
param_type_list(param_type_list(ParamList, '...')) -->
   sequence(param_decl, ",", ParamList), ",...".

param_decl(param_decl(DeclSpecs, Declarator)) -->
   decl_specs(DeclSpecs), declarator(Declarator).
param_decl(param_decl(DeclSpecs, AbstractDeclarator)) -->
   decl_specs(DeclSpecs), abstract_declarator(AbstractDeclarator).
param_decl(param_decl(DeclSpecs)) -->
   decl_specs(DeclSpecs).

initializer(a(AssignmentExp)) -->
   assignment_exp(AssignmentExp).
initializer({InitializerList}) -->
   sequence(initializer, ",", InitializerList).

type_name(type_name(SpecQualifierList, AbstractDeclarator)) -->
   sequence(spec_qualifier, SpecQualifierList), abstract_declarator(AbstractDeclarator).
type_name(type_name(SpecQualifierList)) -->
   sequence(spec_qualifier, SpecQualifierList).

abstract_declarator(pointer(Pointer)) -->
   pointer(Pointer).
abstract_declarator(direct_abstract_declarator(DirectAbstractDeclarator)) -->
   direct_abstract_declarator(DirectAbstractDeclarator).
abstract_declarator(abstract_declarator(Pointer, DirectAbstractDeclarator)) -->
   pointer(Pointer), direct_abstract_declarator(DirectAbstractDeclarator).

direct_abstract_declarator('()'(AbstractDeclarator)) -->
   abstract_declarator(AbstractDeclarator).
direct_abstract_declarator(DirectAbstractDeclarator[ConstExp]) -->
   direct_abstract_declarator(DirectAbstractDeclarator), "[", const_exp(ConstExp), "]".
direct_abstract_declarator([ConstExp]) -->
   "[", const_exp(ConstExp), "]".
direct_abstract_declarator(DirectAbstractDeclarator[]) -->
   direct_abstract_declarator(DirectAbstractDeclarator), "[]".
direct_abstract_declarator([]) -->
   "[]".
direct_abstract_declarator('()'(DirectAbstractDeclarator, ParamTypeList)) -->
   direct_abstract_declarator(DirectAbstractDeclarator),
   "(", param_type_list(ParamTypeList), ")".
direct_abstract_declarator('()'(ParamTypeList)) -->
   "(", param_type_list(ParamTypeList), ")".
direct_abstract_declarator('()'(DirectAbstractDeclarator)) -->
   direct_abstract_declarator(DirectAbstractDeclarator), "()".
direct_abstract_declarator('()') -->
   "()".

typedef_name(Id) -->
   id(Id).

stat(Stat) -->
   labeled_stat(Stat).
stat(Stat) -->
   exp_stat(Stat).
stat(Stat) -->
   compound_stat(Stat).
stat(Stat) -->
   selection_stat(Stat).
stat(Stat) -->
   iteration_stat(Stat).
stat(Stat) -->
   jump_stat(Stat).

labeled_stat(Id:Stat) -->
   id(Id), ":", stat(Stat).
labeled_stat(case(ConstExp:Stat)) -->
   "case ", const_exp(ConstExp), ":", stat(Stat).
labeled_stat(default:Stat) -->
   "default:", stat(Stat).

exp_stat(Exp) -->
   exp(Exp), ";".
exp_stat -->
   ";".

compound_stat({DeclList, StatList}) -->
   "{", sequence(decl, DeclList), sequence(stat, StatList), "}".
compound_stat({StatList}) -->
   "{", sequence(stat, StatList), "}".
compound_stat({DeclList}) -->
   "{", sequence(decl, DeclList), "}".
compound_stat({}) -->
   "{}".

selection_stat(if(Exp, Stat)) -->
   "if(", exp(Exp), ")", stat(Stat).
selection_stat(if(Exp, Stat, Else)) -->
   "if(", exp(Exp), ")", stat(Stat), "else", stat(Else).
selection_stat(switch(Exp, Stat)) -->
   "switch(", exp(Exp), ")", stat(Stat).

iteration_stat(while(Exp, Stat)) -->
   "while(", exp(Exp), ")", stat(Stat).
iteration_stat(do(Stat, Exp)) -->
   "do", stat(Stat), "while(", Exp, ");".
iteration_stat(for(Init, ;, Cond, ;, Inc, Stat)) -->
   "for(", exp(Init), ";", exp(Cond), ";", exp(Inc), ")",
   stat(Stat).
iteration_stat(for(Init, ';', Cond, ';', Stat)) -->
   "for(", exp(Init), ";", exp(Cond), ";", ")",
   stat(Stat).
iteration_stat(for(Init, ;, ;, Inc, Stat)) -->
   "for(", exp(Init), ";", ";", exp(Inc), ")",
   stat(Stat).
iteration_stat(for(Init, ';', ';', Stat)) -->
   "for(", exp(Init), ";", ";", ")",
   stat(Stat).
iteration_stat(for(;, Cond, ;, Inc, Stat)) -->
   "for(", ";", exp(Cond), ";", exp(Inc), ")",
   stat(Stat).
iteration_stat(for(;, Cond, ;, Stat)) -->
   "for(", ";", exp(Cond), ";", ")",
   stat(Stat).
iteration_stat(for(;, ;, Inc, Stat)) -->
   "for(", ";", ";", exp(Inc), ")",
   stat(Stat).
iteration_stat(for(;, ;, Stat)) -->
   "for(", ";", ";", ")",
   stat(Stat).

jump_stat(goto(Id)) -->
   "goto ", id(Id), ";".
jump_stat(continue) -->
   "continue;".
jump_stat(break) -->
   "break;".
jump_stat(return(Exp)) -->
   "return ", exp(Exp).
jump_stat(return) -->
   "return;".

exp(AssignmentExpList) -->
   sequence(assignment_exp, AssignmentExpList).

assignment_exp(a(ConditionalExp)) -->
   conditional_exp(ConditionalExp).
assignment_exp(a(UnaryExp, AssignmentOperator, AssignmentExp)) -->
   unary_exp(UnaryExp), assignment_operator(AssignmentOperator),
   assignment_exp(AssignmentExp).

assignment_operator(=) -->
   "=".
assignment_operator(*=) -->
   "*=".
assignment_operator(/=) -->
   "/=".
assignment_operator('%=') -->
   "%=".
assignment_operator(+=) -->
   "+=".
assignment_operator(-=) -->
   "-=".
assignment_operator(<<=) -->
   "<<=".
assignment_operator(>>=) -->
   ">>=".
assignment_operator(&=) -->
   "&=".
assignment_operator(^=) -->
   "^=".
assignment_operator('|=') -->
   "|=".

conditional_exp(conditional_exp(LogicalOrExp)) -->
   logical_or_exp(LogicalOrExp).
conditional_exp(conditional_exp(LogicalOrExp, Exp, ConditionalExp)) -->
   logical_or_exp(LogicalOrExp), "?", exp(Exp), ":", conditional_exp(ConditionalExp).

const_exp(Exp) -->
   conditional_exp(Exp).

logical_or_exp(logical_or_exp(LogicalAndExp)) -->
   logical_and_exp(LogicalAndExp).
logical_or_exp(logical_or_exp(LogicalOrExp, LogicalAndExp)) -->
   logical_or_exp(LogicalOrExp), "||", logical_and_exp(LogicalAndExp).

logical_and_exp(logical_and_exp(InclusiveOrExp)) -->
   inclusive_or_exp(InclusiveOrExp).
logical_and_exp(logical_and_exp(LogicalAndExp, InclusiveOrExp)) -->
   logical_and_exp(LogicalAndExp), "&&", inclusive_or_exp(InclusiveOrExp).

inclusive_or_exp(inclusive_or_exp(ExclusiveOrExp)) -->
   exclusive_or_exp(ExclusiveOrExp).
inclusive_or_exp(inclusive_or_exp(InclusiveOrExp, ExclusiveOrExp)) -->
   inclusive_or_exp(InclusiveOrExp), "|", exclusive_or_exp(ExclusiveOrExp).

exclusive_or_exp(exclusive_or_exp(AndExp)) -->
   and_exp(AndExp).
exclusive_or_exp(exclusive_or_exp(ExclusiveOrExp, AndExp)) -->
   exclusive_or_exp(ExclusiveOrExp), "^", and_exp(AndExp).

and_exp(and_exp(EqualityExp)) -->
   equality_exp(EqualityExp).
and_exp(and_exp(AndExp, EqualityExp)) -->
   and_exp(AndExp), "&", equality_exp(EqualityExp).

equality_exp(equality_exp(RelationalExp)) -->
   relational_exp(RelationalExp).
equality_exp(EqualityExp == RelationalExp) -->
   equality_exp(EqualityExp), "==", relational_exp(RelationalExp).
equality_exp(dif(EqualityExp, RelationalExp)) -->
   equality_exp(EqualityExp), "!=", relational_exp(RelationalExp).

relational_exp(relational_exp(ShiftExpression)) -->
   shift_expression(ShiftExpression).
relational_exp(RelationalExp < ShiftExpression) -->
   relational_exp(RelationalExp), "<", shift_expression(ShiftExpression).
relational_exp(RelationalExp > ShiftExpression) -->
   relational_exp(RelationalExp), ">", shift_expression(ShiftExpression).
relational_exp(RelationalExp =< ShiftExpression) -->
   relational_exp(RelationalExp), "<=", shift_expression(ShiftExpression).
relational_exp(RelationalExp >= ShiftExpression) -->
   relational_exp(RelationalExp), ">=", shift_expression(ShiftExpression).

shift_expression(shift_expression(AdditiveExp)) -->
   additive_exp(AdditiveExp).
shift_expression(ShiftExpression << AdditiveExp) -->
   shift_expression(ShiftExpression), "<<", additive_exp(AdditiveExp).
shift_expression(ShiftExpression >> AdditiveExp) -->
   shift_expression(ShiftExpression), ">>", additive_exp(AdditiveExp).

additive_exp(additive_exp(MultExp)) -->
   mult_exp(MultExp).
additive_exp(AdditiveExp + MultExp) -->
   additive_exp(AdditiveExp), "+", mult_exp(MultExp).
additive_exp(AdditiveExp - MultExp) -->
   additive_exp(AdditiveExp), "-", mult_exp(MultExp).

mult_exp(mult_exp(CastExp)) -->
   cast_exp(CastExp).
mult_exp(MultExp * CastExp) -->
   mult_exp(MultExp), "*", cast_exp(CastExp).
mult_exp(MultExp / CastExp) -->
   mult_exp(MultExp), "/", cast_exp(CastExp).
mult_exp(MultExp mod CastExp) -->
   mult_exp(MultExp), "%", cast_exp(CastExp).

cast_exp(cast_exp(UnaryExp)) -->
   unary_exp(UnaryExp).
cast_exp(cast_exp(TypeName, CastExp)) -->
   "(", type_name(TypeName), ")", cast_exp(CastExp).

unary_exp(postfix_exp(PostfixExp)) -->
   postfix_exp(PostfixExp).
unary_exp('++'(UnaryExp)) -->
   "++", unary_exp(UnaryExp).
unary_exp('--'(UnaryExp)) -->
   "--", unary_exp(UnaryExp).
unary_exp(a(UnaryOperator, CastExp)) -->
   unary_operator(UnaryOperator), cast_exp(CastExp).
unary_exp(sizeof(UnaryExp)) -->
   "sizeof", unary_exp(UnaryExp).
unary_exp(sizeof('()'(TypeName))) -->
   "sizeof(", type_name(TypeName), ")".

unary_operator(&) -->
   "&".
unary_operator(*) -->
   "*".
unary_operator(+) -->
   "+".
unary_operator(-) -->
   "-".
unary_operator(~) -->
   "~".
unary_operator(!) -->
   "!".

postfix_exp(a(PrimaryExp)) -->
   primary_exp(PrimaryExp).
postfix_exp(PostfixExp[Exp]) -->
   postfix_exp(PostfixExp), "[", exp(Exp), "]".
postfix_exp('()'(PostfixExp, ArgumentExpList)) -->
   postfix_exp(PostfixExp), "(", argument_exp_list(ArgumentExpList), ")".
postfix_exp('()'(PostfixExp)) -->
   postfix_exp(PostfixExp), "()".
postfix_exp('.'(PostfixExp, Id)) -->
   postfix_exp(PostfixExp), ".", id(Id).
postfix_exp('->'(PostfixExp, Id)) -->
   postfix_exp(PostfixExp), "->", id(Id).
postfix_exp('++'(PostfixExp)) -->
   postfix_exp(PostfixExp), "++".
postfix_exp('--'(PostfixExp)) -->
   postfix_exp(PostfixExp), "--".

primary_exp(id(Id)) -->
   id(Id).
primary_exp(const(Const)) -->
   const(Const).
primary_exp(string(String)) -->
   string(String).
primary_exp('()'(Exp)) -->
   "(", exp(Exp), ")".

argument_exp_list(ArgumentExpList) -->
   sequence(assignment_exp, ",", ArgumentExpList).

const(int(Int)) -->
   integer(Int).
const(char(Char)) -->
   [Char].
const(float(Float)) -->
   float(Float).
