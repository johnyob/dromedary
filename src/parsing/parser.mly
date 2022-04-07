/*****************************************************************************/
/*                                                                           */
/*                                Dromedary                                  */
/*                                                                           */
/*                Alistair O'Brien, University of Cambridge                  */
/*                                                                           */
/* Copyright 2021 Alistair O'Brien.                                          */
/*                                                                           */
/* All rights reserved. This file is distributed under the terms of the MIT  */
/* license, as described in the file LICENSE.                                */
/*                                                                           */
/*****************************************************************************/

// end of file
%token EOF

// keywords
%token LET
%token REC
%token AND
%token IN
%token IF
%token THEN 
%token ELSE
%token FUN
%token WHILE
%token DO
%token DONE
%token FOR
%token TO
%token DOWNTO
%token TRY
%token WITH
%token MATCH
%token FORALL 
%token EXISTS
%token TYPE
%token AS
%token OF
%token EXCEPTION
%token EXTERNAL
%token CONSTRAINT
%token SEMI_SEMI_COLON

// operators / special
%token RIGHT_ARROW
%token COLON
%token EQUAL
%token DOT
%token COMMA
%token SEMI_COLON
%token STAR
%token UNDERSCORE
%token QUOTE
%token BACKTICK
%token BAR

// primitives
%token REF
%token OP_ASSIGN
%token OP_DEREF
// %token OP_NOT_EQUAL
// %token OP_LESS_EQUAL
// %token OP_LESS
// %token OP_GREATER_EQUAL
// %token OP_GREATER
// %token OP_OR
// %token OP_AND
// %token OP_FTIMES
// %token OP_FPLUS
// %token OP_FMINUS
// %token OP_FDIVIDE
// %token OP_FEXP
%token OP_PLUS
%token OP_MINUS
%token OP_DIVIDE

// literals
%token TRUE
%token FALSE
%token <char> CHAR
%token <string> STRING
%token <int> INT
%token <float> FLOAT
%token UNIT

// identifiers
%token <string> IDENT
%token <string> CON_IDENT

// parens
%token LEFT_PAREN
%token RIGHT_PAREN
%token LEFT_BRACE
%token RIGHT_BRACE

// infix syntax
// %nonassoc IN
%nonassoc prec_below_SEMI
%nonassoc SEMI_COLON
// %nonassoc LET
// %nonassoc WITH
// %nonassoc AND
// %nonassoc THEN
// %nonassoc ELSE
%nonassoc AS
// %nonassoc BAR

// binary operators
// %right RIGHT_ARROW
// %nonassoc prec_below_EQUAL
%right OP_ASSIGN
%left EQUAL
%left OP_PLUS OP_MINUS
%left STAR OP_DIVIDE
%nonassoc prec_unary_op
%nonassoc prec_construct_app

// %nonassoc INT TRUE FALSE UNIT
          // LEFT_PAREN
          // IDENT CON_IDENT UNDERSCORE
          


%{
open Ast_types
open Parsetree

let unary_op ~op ~exp = 
  Pexp_app (Pexp_prim op, exp)

let bin_op ~op ~exp1 ~exp2 = 
  Pexp_app (Pexp_app (Pexp_prim op, exp1), exp2)

let rec fun_ ~pats ~exp = 
  match pats with
  | [] -> assert false
  | [ pat ] -> Pexp_fun (pat, exp)
  | pat :: pats -> Pexp_fun (pat, fun_ ~pats ~exp)

let exn_decl ~con ~arg =
  let arg =
    Option.map
      (fun arg ->
      { pconstructor_arg_betas = []; pconstructor_arg_type = arg })
      arg
  in
  let constr_decl =
    { pconstructor_name = con
    ; pconstructor_arg = arg
    ; pconstructor_constraints = []
    }
  in
  let ext_constr =
    { pext_name = "exn"; pext_params = []; pext_kind = Pext_decl constr_decl }
  in
  { ptyexn_constructor = ext_constr }

%}


%start parse_structure parse_expression
%type <structure> parse_structure
%type <expression> parse_expression

%type <structure_item> structure_item

%type <rec_flag> rec_flag
%type <constant> constant
%type <primitive> bin_op
%type <primitive> unary_op
%type <direction_flag> direction_flag

%type <string> type_var
%type <core_type> core_type
%type <core_type> tuple_type
%type <core_type> atom_type
%type <core_type list> type_argument_list


%type <expression> seq_expression
%type <expression> expression
%type <expression> atom_expression

%type <value_binding list> value_bindings
%type <value_binding> value_binding

%type <case list> cases
%type <case> case

%type <string * expression> record_assignment

%type <pattern> pattern_var

%type <pattern> pattern
// %type <pattern> construct_pattern
%type <pattern> atom_pattern
// %type <string list * pattern> con_pattern_arg

%%

// Generic definitions


// [seperated_nontrivial_list(sep, X)] parases a list containing 
// at least two [X]s separated by [sep].

separated_nontrivial_list(sep, X):
  | x1 = X
    ; sep
    ; x2 = X
      { [ x1; x2 ] }
  | x = X
    ; sep
    ; xs = separated_nontrivial_list(sep, X)
      { x :: xs }

// [preceded_or_separated_nonempty_list(sep, X)]
%inline preceded_or_separated_nonempty_list(sep, X):
  | ioption(sep); xs = separated_nonempty_list(sep, X)  { xs }

// Parsing

parse_structure:
  structure EOF { $1 }


parse_expression:
  expression EOF { $1 }

rec_flag:
  | /* empty */   { Nonrecursive }
  | REC           { Recursive }

constant:
  | int_ = INT      { Const_int int_ }
  | float = FLOAT   { Const_float float }
  | TRUE            { Const_bool true }
  | FALSE           { Const_bool false }
  | string = STRING { Const_string string }
  | char = CHAR     { Const_char char }
  | UNIT            { Const_unit }

%inline type_var:
  QUOTE; id = IDENT         { id }

core_type:
  | core_type = tuple_type
      { core_type }   
  | core_type1 = tuple_type
    ; RIGHT_ARROW
    ; core_type2 = core_type
      { Ptyp_arrow (core_type1, core_type2) }

tuple_type:
  | core_type = atom_type
      { core_type }
  | core_types = separated_nontrivial_list(STAR, atom_type)
      { Ptyp_tuple core_types }

atom_type:
  | LEFT_PAREN
    ; core_type = core_type
    ; RIGHT_PAREN
      { core_type }
  | var = type_var
      { Ptyp_var var }
  | core_types = type_argument_list
    ; id = IDENT
      { Ptyp_constr (core_types, id) }

%inline type_argument_list:
  | /* empty */   
      { [] }
  | core_type = atom_type 
      { [ core_type ] }
  | LEFT_PAREN
    ; core_types = separated_nontrivial_list(COMMA, core_type)
    ; RIGHT_PAREN
      { core_types }

%inline type_param_list:
  | /* empty */   
      { [] }
  | type_var = type_var 
      { [ type_var ] }
  | LEFT_PAREN
    ; type_vars = separated_nontrivial_list(COMMA, type_var)
    ; RIGHT_PAREN
      { type_vars }

seq_expression:
  | expression %prec prec_below_SEMI     { $1 }
  | expression SEMI_COLON seq_expression  { Pexp_sequence ($1, $3) }

expression:
  | exp = app_expression                                                                   
      { exp }
  | op = unary_op; exp = expression %prec prec_unary_op
      { unary_op ~op ~exp }
  | exp1 = expression; op = bin_op; exp2 = expression
      { bin_op ~op ~exp1 ~exp2 }
  | IF
    ; cond = expression
    ; THEN
    ; then_ = seq_expression
    ; ELSE
    ; else_ = seq_expression
      { Pexp_ifthenelse (cond, then_, else_) }
  | WHILE; exp1 = expression; DO; exp2 = seq_expression; DONE
      { Pexp_while (exp1, exp2) }
  | FOR
    ; pat = pattern_var
    ; EQUAL
    ; exp1 = expression
    ; dir_flag = direction_flag
    ; exp2 = expression
    ; DO
    ; exp3 = seq_expression
    ; DONE
      { Pexp_for (pat, exp1, exp2, dir_flag, exp3) }
  | FUN; pats = nonempty_list(atom_pattern); RIGHT_ARROW; exp = seq_expression 
      { fun_ ~pats ~exp }
  | FORALL
    ; LEFT_PAREN
    ; TYPE
    ; type_vars = nonempty_list(type_var)
    ; RIGHT_PAREN
    ; RIGHT_ARROW
    ; exp = seq_expression
      { Pexp_forall (type_vars, exp) }
  | EXISTS
    ; LEFT_PAREN
    ; TYPE
    ; type_vars = nonempty_list(type_var)
    ; RIGHT_PAREN
    ; RIGHT_ARROW
    ; exp = seq_expression
      { Pexp_exists (type_vars, exp) }
  | TRY 
    ; exp = expression 
    ; WITH 
    ; cases = cases
      { Pexp_try (exp, cases) }
  | MATCH 
    ; exp = expression 
    ; WITH 
    ; cases = cases
      { Pexp_match (exp, cases) }
  | LET
    ; rec_flag = rec_flag
    ; value_bindings = value_bindings
    ; IN
    ; exp = seq_expression
      { Pexp_let (rec_flag, value_bindings, exp) }

app_expression:
  | exp = atom_expression
    { exp }
  | exp1 = app_expression; exp2 = atom_expression
    { match exp1 with
      | Pexp_construct (con_id, None) -> Pexp_construct (con_id, Some exp2)
      | Pexp_variant (tag, None) -> Pexp_variant (tag, Some exp2)
      | _ -> Pexp_app (exp1, exp2)
    }

%inline value_bindings:
  value_bindings = separated_nonempty_list(AND, value_binding)
    { value_bindings }

%inline value_binding_type_vars:
  | /* empty */   
    { [] }
  | LEFT_PAREN
    ; TYPE
    ; type_vars = nonempty_list(type_var)
    ; RIGHT_PAREN
      { type_vars }  

value_binding:
  type_vars = value_binding_type_vars
  ; pat = pattern 
  ; EQUAL
  ; exp = seq_expression
    { {pvb_forall_vars = type_vars; pvb_pat = pat; pvb_expr = exp } }

%inline cases:
  LEFT_PAREN
  ; cases = preceded_or_separated_nonempty_list(BAR, case)
  ; RIGHT_PAREN
    { cases }

case:
  pat = pattern
  ; RIGHT_ARROW
  ; exp = seq_expression
      { { pc_lhs = pat; pc_rhs = exp } }


atom_expression:
  | const = constant 
      { Pexp_const const }
  | id = IDENT
      { Pexp_var id }
  | exp = atom_expression; DOT; label = IDENT
      { Pexp_field (exp, label) }
  | con_id = CON_IDENT
      { Pexp_construct (con_id, None) }
  | BACKTICK; tag = CON_IDENT
      { Pexp_variant (tag, None) } 
  | LEFT_PAREN
    ; exps = separated_nontrivial_list(COMMA, seq_expression)
    ; RIGHT_PAREN
      { Pexp_tuple exps }
  | LEFT_BRACE
    ; label_exps = separated_nonempty_list(SEMI_COLON, record_assignment)
    ; RIGHT_BRACE
      { Pexp_record label_exps }
  | LEFT_PAREN
    ; exp = seq_expression
    ; COLON
    ; core_type = core_type
    ; RIGHT_PAREN
      { Pexp_constraint (exp, core_type) }
  | LEFT_PAREN
    ; exp = seq_expression
    RIGHT_PAREN
      { exp }

%inline record_assignment:
  label = IDENT
  ; EQUAL
  ; exp = expression
    { (label, exp) }

%inline direction_flag:
  | TO      { Upto }
  | DOWNTO  { Downto }

%inline unary_op:
  | OP_DEREF    { Prim_deref }
  | REF         { Prim_ref }

%inline bin_op:
  | EQUAL       { Prim_eq }
  | OP_ASSIGN   { Prim_assign }
  | OP_PLUS     { Prim_add }
  | OP_MINUS    { Prim_sub }
  | OP_DIVIDE   { Prim_div }
  | STAR        { Prim_mul }

pattern_var:
  | UNDERSCORE
      { Ppat_any }
  | id = IDENT
      { Ppat_var id }

pattern:
  | pat = construct_pattern
      { pat }
  | pat = pattern; AS; id = IDENT
      { Ppat_alias (pat, id) }

construct_pattern:
  | pat = atom_pattern
      { pat }
  | con_id = CON_IDENT
    ; con_pat_arg = con_pattern_arg %prec prec_construct_app
      { Ppat_construct (con_id, Some con_pat_arg) }

atom_pattern:
  | const = constant
      { Ppat_const const }
  | UNDERSCORE      
      { Ppat_any }
  | id = IDENT            
      { Ppat_var id }
  | con_id = CON_IDENT
      { Ppat_construct (con_id, None) }
  | LEFT_PAREN 
    ; pats = separated_nontrivial_list(COMMA, pattern)
    ; RIGHT_PAREN
      { Ppat_tuple pats }
  | LEFT_PAREN
    ; pat = pattern
    ; COLON
    ; core_type = core_type
    ; RIGHT_PAREN
      { Ppat_constraint (pat, core_type) }
  | LEFT_PAREN
    ; pat = pattern
    ; RIGHT_PAREN
      { pat }  

%inline con_pattern_arg_type_vars:
  | /* empty */   
    { [] }
  | LEFT_PAREN
    ; TYPE
    ; type_vars = nonempty_list(type_var)
    ; RIGHT_PAREN
      { type_vars }  

%inline con_pattern_arg:
  | type_vars = con_pattern_arg_type_vars
    ; pat = pattern
      { (type_vars, pat) }

%inline core_scheme:
  | type_vars = nonempty_list(type_var)
    ; DOT
    ; type_ = core_type
      { (type_vars, type_) }
  | type_ = core_type
      { ([], type_) }

type_declarations:
  | TYPE; decls = separated_nonempty_list(AND, type_declaration)
      { decls }

%inline type_declaration:
  | params = type_param_list; id = IDENT; kind = type_decl_kind
      { { ptype_name = id; ptype_params = params; ptype_kind = kind } }

type_decl_kind:
  | /* empty */
      { Ptype_abstract }
  | EQUAL; constr_decls = preceded_or_separated_nonempty_list(BAR, constructor_declaration)
      { Ptype_variant constr_decls }
  | EQUAL; LEFT_BRACE
    ; label_decls = separated_nonempty_list(SEMI_COLON, label_declaration)
    ; RIGHT_BRACE
      { Ptype_record label_decls }
  | EQUAL; type_ = core_type
      { Ptype_alias type_ }

%inline label_declaration:
  | label = IDENT
    ; COLON
    ; scheme = core_scheme
      { let betas, arg = scheme in
        { plabel_name = label; plabel_betas = betas; plabel_arg = arg } }

%inline constructor_declaration:
  | con_id = CON_IDENT
    ; arg = option(constructor_argument)
    ; constraints = constraints
      { { pconstructor_name = con_id; pconstructor_arg = arg; pconstructor_constraints = constraints } }


%inline constructor_argument:
  | OF
    ; scheme = core_scheme
      { let betas, arg = scheme in
        { pconstructor_arg_betas = betas; pconstructor_arg_type = arg } }

%inline constraint_:
  | type1 = core_type
    ; EQUAL
    ; type2 = core_type
      { (type1, type2) }

constraints:
  | /* empty */     { [] }
  | CONSTRAINT
    ; constraints = separated_nonempty_list(AND, constraint_)
      { constraints }

%inline exception_argument:
  | OF; arg = core_type
      { arg }

%inline exception_declaration:
  | con_id = CON_IDENT
    ; arg = option(exception_argument)
      { exn_decl ~con:con_id ~arg }

structure_item:
  | LET
    ; rec_flag = rec_flag
    ; value_bindings = value_bindings
      { Pstr_value (rec_flag, value_bindings) }
  | EXTERNAL
    ; id = IDENT
    ; COLON
    ; scheme = core_scheme
    ; EQUAL
    ; prim = STRING
      { Pstr_primitive { pval_name = id; pval_type = scheme; pval_prim = prim } }
  | type_decls = type_declarations
      { Pstr_type type_decls }
  | EXCEPTION
    ; exn_decl = exception_declaration
      { Pstr_exception exn_decl }

%inline terminated_structure_item:
  | str_item = structure_item
    ; SEMI_SEMI_COLON
      { str_item }


structure:
  | structure = nonempty_list(terminated_structure_item)
      { structure }
