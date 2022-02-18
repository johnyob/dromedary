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

%{


open Parsetree
%}

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

// operators
%token RIGHT_ARROW
%token COLON
%token EQUAL
%token DOT
%token COMMA
%token SEMI_COLON
%token STAR

// primitives
%token REF
%token OP_ASSIGN
%token OP_DEREF
%token OP_NOT_EQUAL
%token OP_LESS_EQUAL
%token OP_LESS
%token OP_GREATER_EQUAL
%token OP_GREATER
%token OP_OR
%token OP_AND
%token OP_FTIMES
%token OP_FPLUS
%token OP_FMINUS
%token OP_FDIVIDE
%token OP_FEXP
%token OP_PLUS
%token OP_MINUS
%token OP_DIVIDE

// literals
%token <bool> BOOL
%token <int> INT
%token <float> FLOAT
%token UNIT

// identifiers
%token <string> IDENT
%token <string> CON_IDENT

%start expression
%type <expression> expression

%%

// stub
expression:
  EOF { Pexp_var "x" }