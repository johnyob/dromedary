open! Import
open Util

let%expect_test "unterminated string" =
  let str = {| "hello world |} in
  print_tokens str;
  [%expect {| "lexer error: String is not terminated" |}]

let%expect_test "unterminated comment" =
  let str = {| (* This is a very interesting comment |} in
  print_tokens str;
  [%expect {| "lexer error: Unclosed comment" |}]

let%expect_test "single-line comment" =
  let str = {| (* Some comment here *) |} in
  print_tokens str;
  [%expect {| |}]

let%expect_test "multi-line comment" =
  let str =
    {| 
      (* This is a very long 
         and interesting comment 
      *) 
    |}
  in
  print_tokens str;
  [%expect {| |}]

let%expect_test "keywords" =
  [ "let"
  ; "rec"
  ; "and"
  ; "in"
  ; "if"
  ; "then"
  ; "else"
  ; "fun"
  ; "while"
  ; "do"
  ; "done"
  ; "for"
  ; "to"
  ; "downto"
  ; "try"
  ; "with"
  ; "match"
  ; "forall"
  ; "exists"
  ; "type"
  ; "as"
  ; "of"
  ; "exception"
  ; "external"
  ; "constraint"
  ; ";;"
  ; "->"
  ; ":"
  ; "="
  ; "."
  ; ","
  ; ";"
  ; "*"
  ; "_"
  ; "'"
  ; "`"
  ; "|"
  ; "ref"
  ; ":="
  ; "!"
  ; "+"
  ; "-"
  ; "/"
  ; "true"
  ; "false"
  ; "()"
  ; "("
  ; ")"
  ; "{"
  ; "}"
  ; "["
  ; "]"
  ; "<"
  ; ">"
  ; "mu"
  ; "where"
  ]
  |> List.iter ~f:(fun keyword ->
         Format.fprintf Format.std_formatter "Keyword: %s @.Output: " keyword;
         print_tokens keyword);
  [%expect
    {|
    Keyword: let
    Output: LET
    Keyword: rec
    Output: REC
    Keyword: and
    Output: AND
    Keyword: in
    Output: IN
    Keyword: if
    Output: IF
    Keyword: then
    Output: THEN
    Keyword: else
    Output: ELSE
    Keyword: fun
    Output: FUN
    Keyword: while
    Output: WHILE
    Keyword: do
    Output: DO
    Keyword: done
    Output: DONE
    Keyword: for
    Output: FOR
    Keyword: to
    Output: TO
    Keyword: downto
    Output: DOWNTO
    Keyword: try
    Output: TRY
    Keyword: with
    Output: WITH
    Keyword: match
    Output: MATCH
    Keyword: forall
    Output: FORALL
    Keyword: exists
    Output: EXISTS
    Keyword: type
    Output: TYPE
    Keyword: as
    Output: AS
    Keyword: of
    Output: OF
    Keyword: exception
    Output: EXCEPTION
    Keyword: external
    Output: EXTERNAL
    Keyword: constraint
    Output: CONSTRAINT
    Keyword: ;;
    Output: SEMI_SEMI_COLON
    Keyword: ->
    Output: RIGHT_ARROW
    Keyword: :
    Output: COLON
    Keyword: =
    Output: EQUAL
    Keyword: .
    Output: DOT
    Keyword: ,
    Output: COMMA
    Keyword: ;
    Output: SEMI_COLON
    Keyword: *
    Output: STAR
    Keyword: _
    Output: UNDERSCORE
    Keyword: '
    Output: QUOTE
    Keyword: `
    Output: BACKTICK
    Keyword: |
    Output: BAR
    Keyword: ref
    Output: REF
    Keyword: :=
    Output: OP_ASSIGN
    Keyword: !
    Output: OP_DEREF
    Keyword: +
    Output: OP_PLUS
    Keyword: -
    Output: OP_MINUS
    Keyword: /
    Output: OP_DIVIDE
    Keyword: true
    Output: TRUE
    Keyword: false
    Output: FALSE
    Keyword: ()
    Output: UNIT
    Keyword: (
    Output: LEFT_PAREN
    Keyword: )
    Output: RIGHT_PAREN
    Keyword: {
    Output: LEFT_BRACE
    Keyword: }
    Output: RIGHT_BRACE
    Keyword: [
    Output: LEFT_BRACKET
    Keyword: ]
    Output: RIGHT_BRACKET
    Keyword: <
    Output: LESS
    Keyword: >
    Output: GREATER
    Keyword: mu
    Output: MU
    Keyword: where
    Output: WHERE |}]

let%expect_test "string" =
  let str = {| "some string" |} in
  print_tokens str;
  [%expect {| STRING(some string) |}]

let%expect_test "string - escape chars" =
  let str =
    {| 
      "Standard: Hello world!\n String:\"String within a string\"\n Char:\'c\'\n Tab:\t test" 
    |}
  in
  print_tokens str;
  [%expect
    {|
    STRING(Standard: Hello world!
     String:"String within a string"
     Char:'c'
     Tab:	 test) |}]

let%expect_test "char" =
  let str = {| 'a' 'b' 'c' 'd' 'e' |} in
  print_tokens str;
  [%expect {|
    CHAR(a)
    CHAR(b)
    CHAR(c)
    CHAR(d)
    CHAR(e) |}]

let%expect_test "char - escape chars" =
  let str = {| 
      '\t' '\n' '\"' '\'' '\\' 
    |} in
  print_tokens str;
  [%expect {|
  CHAR(	)
  CHAR(
  )
  CHAR(")
  CHAR(')
  CHAR(\) |}]

let%expect_test "ints" =
  [ "1"; "0"; "0123456789"; "-42" ]
  |> List.iter ~f:(fun int_ ->
         Format.fprintf Format.std_formatter "Int: %s @.Output: " int_;
         print_tokens int_);
  [%expect
    {|
    Int: 1
    Output: INT(1)
    Int: 0
    Output: INT(0)
    Int: 0123456789
    Output: INT(123456789)
    Int: -42
    Output: INT(-42) |}]

let%expect_test "floats" =
  [ "1."; "-42."; ".66"; "-.1"; "-.28190328901"; "3.99999"; "4.0"; "-4.0" ]
  |> List.iter ~f:(fun float_ ->
         Format.fprintf Format.std_formatter "Float: %s @.Output: " float_;
         print_tokens float_);
  [%expect
    {|
    Float: 1.
    Output: FLOAT(1.000000)
    Float: -42.
    Output: FLOAT(-42.000000)
    Float: .66
    Output: FLOAT(0.660000)
    Float: -.1
    Output: FLOAT(-0.100000)
    Float: -.28190328901
    Output: FLOAT(-0.281903)
    Float: 3.99999
    Output: FLOAT(3.999990)
    Float: 4.0
    Output: FLOAT(4.000000)
    Float: -4.0
    Output: FLOAT(-4.000000) |}]

let%expect_test "lident" =
  [ "x"
  ; "type_"
  ; "lident"
  ; "x1"
  ; "snake_case"
  ; "prime'"
  ; "prime_numbers10998927898723178923''''"
  ]
  |> List.iter ~f:(fun lident ->
         Format.fprintf Format.std_formatter "Lident: %s @.Output: " lident;
         print_tokens lident);
  [%expect
    {|
    Lident: x
    Output: IDENT(x)
    Lident: type_
    Output: IDENT(type_)
    Lident: lident
    Output: IDENT(lident)
    Lident: x1
    Output: IDENT(x1)
    Lident: snake_case
    Output: IDENT(snake_case)
    Lident: prime'
    Output: IDENT(prime')
    Lident: prime_numbers10998927898723178923''''
    Output: IDENT(prime_numbers10998927898723178923'''') |}]

let%expect_test "uident" =
  [ "X"
  ; "Cons"
  ; "Nil"
  ; "Cannot_unify"
  ; "Left_brace"
  ; "Prime'"
  ; "Primes''''"
  ; "Numbers1029347583"
  ; "Everything_1234_foo_bar''''''"
  ]
  |> List.iter ~f:(fun lident ->
         Format.fprintf Format.std_formatter "Lident: %s @.Output: " lident;
         print_tokens lident);
  [%expect {|
    Lident: X
    Output: CON_IDENT(X)
    Lident: Cons
    Output: CON_IDENT(Cons)
    Lident: Nil
    Output: CON_IDENT(Nil)
    Lident: Cannot_unify
    Output: CON_IDENT(Cannot_unify)
    Lident: Left_brace
    Output: CON_IDENT(Left_brace)
    Lident: Prime'
    Output: CON_IDENT(Prime')
    Lident: Primes''''
    Output: CON_IDENT(Primes'''')
    Lident: Numbers1029347583
    Output: CON_IDENT(Numbers1029347583)
    Lident: Everything_1234_foo_bar''''''
    Output: CON_IDENT(Everything_1234_foo_bar'''''') |}]
