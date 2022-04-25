open! Import
open Util

let%expect_test "top level function definition" =
  let str = 
    {| 
      let smallest_integer = 0;;
    |} 
  in
  print_structure_parsetree str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Let: Nonrecursive
          └──Value bindings:
             └──Value binding:
                └──Pattern: Variable: smallest_integer
                └──Expression: Constant: 0 |}]

let%expect_test "multiple nonrecursive top level definitions" =
  let str = 
    {|
      let smallest_integer = 0 
      and () = print_endline "Hello world!";;
    |}
  in
  print_structure_parsetree str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Let: Nonrecursive
          └──Value bindings:
             └──Value binding:
                └──Pattern: Variable: smallest_integer
                └──Expression: Constant: 0
             └──Value binding:
                └──Pattern: Constant: ()
                └──Expression: Application
                   └──Expression: Variable: print_endline
                   └──Expression: Constant: Hello world! |}]

let%expect_test "recursive top level definitions" =
  let str = 
    {|
      let rec map = fun t f ->
        match t with
        ( Nil -> Nil
        | Cons (x, t) -> Cons (f x, map t f)
        )
      and double = 
        fun t -> map t (fun x -> x * 2)
      ;;
    |}
  in
  print_structure_parsetree str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Let: Recursive
          └──Value bindings:
             └──Value binding:
                └──Pattern: Variable: map
                └──Expression: Function
                   └──Pattern: Variable: t
                   └──Expression: Function
                      └──Pattern: Variable: f
                      └──Expression: Match
                         └──Expression: Variable: t
                         └──Cases:
                            └──Case:
                               └──Pattern: Construct
                                  └──Constructor: Nil
                               └──Expression: Construct
                                  └──Constructor: Nil
                            └──Case:
                               └──Pattern: Construct
                                  └──Constructor: Cons
                                  └──Pattern: Tuple
                                     └──Pattern: Variable: x
                                     └──Pattern: Variable: t
                               └──Expression: Construct
                                  └──Constructor: Cons
                                  └──Expression: Tuple
                                     └──Expression: Application
                                        └──Expression: Variable: f
                                        └──Expression: Variable: x
                                     └──Expression: Application
                                        └──Expression: Application
                                           └──Expression: Variable: map
                                           └──Expression: Variable: t
                                        └──Expression: Variable: f
             └──Value binding:
                └──Pattern: Variable: double
                └──Expression: Function
                   └──Pattern: Variable: t
                   └──Expression: Application
                      └──Expression: Application
                         └──Expression: Variable: map
                         └──Expression: Variable: t
                      └──Expression: Function
                         └──Pattern: Variable: x
                         └──Expression: Application
                            └──Expression: Application
                               └──Expression: Primitive: (*)
                               └──Expression: Variable: x
                            └──Expression: Constant: 2 |}]


let%expect_test "type definitions - ADTs" =
  let str =
    {|
      type 'a list = 
        | Nil (* empty list - "nil" *)
        | Cons of 'a * 'a list (* list constructor - "cons" *)
      ;;
    |}
  in
  print_structure_parsetree str;
  [%expect
    {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: list
             └──Type parameters: a
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor argument:
                      └──Constructor existentials:
                      └──Type: Tuple
                         └──Type: Variable
                            └──Variable: a
                         └──Type: Constructor
                            └──Constructor: list
                            └──Type: Variable
                               └──Variable: a |}]

let%expect_test "type definition - records" =
  let str =
    {|
      type part = 
        | Part_ia
        | Part_ib
        | Part_ii
      ;;

      type course = Types;;

      type student = 
        { crsid : string 
        ; part : part
        ; courses : course list
        }
      ;;
    |}
  in
  print_structure_parsetree str;
  [%expect
    {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: part
             └──Type parameters:
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Part_ia
                └──Constructor declaration:
                   └──Constructor name: Part_ib
                └──Constructor declaration:
                   └──Constructor name: Part_ii
       └──Structure item: Type
          └──Type declaration:
             └──Type name: course
             └──Type parameters:
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Types
       └──Structure item: Type
          └──Type declaration:
             └──Type name: student
             └──Type parameters:
             └──Type declaration kind: Record
                └──Label declaration:
                   └──Label name: crsid
                   └──Label polymorphic parameters:
                   └──Type: Constructor
                      └──Constructor: string
                └──Label declaration:
                   └──Label name: part
                   └──Label polymorphic parameters:
                   └──Type: Constructor
                      └──Constructor: part
                └──Label declaration:
                   └──Label name: courses
                   └──Label polymorphic parameters:
                   └──Type: Constructor
                      └──Constructor: list
                      └──Type: Constructor
                         └──Constructor: course |}]


let%expect_test "type definition - GADTs" =
  let str = 
    {|
      type 'a term =
        | Int of int constraint 'a = int
        | Bool of bool constraint 'a = int
        | Pair of 'b 'c. 'b term * 'c term constraint 'a = 'b * 'c
        | Fst of 'b. ('a * 'b) term
        | Snd of 'b. ('b * 'a) term
        | If of bool term * 'a term * 'a term
      ;;
    |}
  in
  print_structure_parsetree str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: term
             └──Type parameters: a
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Int
                   └──Constructor argument:
                      └──Constructor existentials:
                      └──Type: Constructor
                         └──Constructor: int
                   └──Constraint:
                      └──Type: Variable
                         └──Variable: a
                      └──Type: Constructor
                         └──Constructor: int
                └──Constructor declaration:
                   └──Constructor name: Bool
                   └──Constructor argument:
                      └──Constructor existentials:
                      └──Type: Constructor
                         └──Constructor: bool
                   └──Constraint:
                      └──Type: Variable
                         └──Variable: a
                      └──Type: Constructor
                         └──Constructor: int
                └──Constructor declaration:
                   └──Constructor name: Pair
                   └──Constructor argument:
                      └──Constructor existentials: b c
                      └──Type: Tuple
                         └──Type: Constructor
                            └──Constructor: term
                            └──Type: Variable
                               └──Variable: b
                         └──Type: Constructor
                            └──Constructor: term
                            └──Type: Variable
                               └──Variable: c
                   └──Constraint:
                      └──Type: Variable
                         └──Variable: a
                      └──Type: Tuple
                         └──Type: Variable
                            └──Variable: b
                         └──Type: Variable
                            └──Variable: c
                └──Constructor declaration:
                   └──Constructor name: Fst
                   └──Constructor argument:
                      └──Constructor existentials: b
                      └──Type: Constructor
                         └──Constructor: term
                         └──Type: Tuple
                            └──Type: Variable
                               └──Variable: a
                            └──Type: Variable
                               └──Variable: b
                └──Constructor declaration:
                   └──Constructor name: Snd
                   └──Constructor argument:
                      └──Constructor existentials: b
                      └──Type: Constructor
                         └──Constructor: term
                         └──Type: Tuple
                            └──Type: Variable
                               └──Variable: b
                            └──Type: Variable
                               └──Variable: a
                └──Constructor declaration:
                   └──Constructor name: If
                   └──Constructor argument:
                      └──Constructor existentials:
                      └──Type: Tuple
                         └──Type: Constructor
                            └──Constructor: term
                            └──Type: Constructor
                               └──Constructor: bool
                         └──Type: Constructor
                            └──Constructor: term
                            └──Type: Variable
                               └──Variable: a
                         └──Type: Constructor
                            └──Constructor: term
                            └──Type: Variable
                               └──Variable: a |}]

let%expect_test "type definition - GADT" =
  let str = 
    {|
      type 'a key = 
        | Int of int constraint 'a = string
        | Float of float constraint 'a = bool
      ;;

      type elem = Elem of 'value. 'value key * 'value;;
    |}
  in
  print_structure_parsetree str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: key
             └──Type parameters: a
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Int
                   └──Constructor argument:
                      └──Constructor existentials:
                      └──Type: Constructor
                         └──Constructor: int
                   └──Constraint:
                      └──Type: Variable
                         └──Variable: a
                      └──Type: Constructor
                         └──Constructor: string
                └──Constructor declaration:
                   └──Constructor name: Float
                   └──Constructor argument:
                      └──Constructor existentials:
                      └──Type: Constructor
                         └──Constructor: float
                   └──Constraint:
                      └──Type: Variable
                         └──Variable: a
                      └──Type: Constructor
                         └──Constructor: bool
       └──Structure item: Type
          └──Type declaration:
             └──Type name: elem
             └──Type parameters:
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Elem
                   └──Constructor argument:
                      └──Constructor existentials: value
                      └──Type: Tuple
                         └──Type: Constructor
                            └──Constructor: key
                            └──Type: Variable
                               └──Variable: value
                         └──Type: Variable
                            └──Variable: value |}]

let%expect_test "type definition - poly records" =
  let str = 
    {|
      type elem_mapper = 
        { f : 'value. 'value key -> 'value -> 'value }
      ;;

      let map_elem = fun (Elem (key, value)) mapper ->
        Elem (key, mapper.f key value)
      ;;

      type t = elem list;;
    |}
  in
  print_structure_parsetree str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: elem_mapper
             └──Type parameters:
             └──Type declaration kind: Record
                └──Label declaration:
                   └──Label name: f
                   └──Label polymorphic parameters: value
                   └──Type: Arrow
                      └──Type: Constructor
                         └──Constructor: key
                         └──Type: Variable
                            └──Variable: value
                      └──Type: Arrow
                         └──Type: Variable
                            └──Variable: value
                         └──Type: Variable
                            └──Variable: value
       └──Structure item: Let: Nonrecursive
          └──Value bindings:
             └──Value binding:
                └──Pattern: Variable: map_elem
                └──Expression: Function
                   └──Pattern: Construct
                      └──Constructor: Elem
                      └──Pattern: Tuple
                         └──Pattern: Variable: key
                         └──Pattern: Variable: value
                   └──Expression: Function
                      └──Pattern: Variable: mapper
                      └──Expression: Construct
                         └──Constructor: Elem
                         └──Expression: Tuple
                            └──Expression: Variable: key
                            └──Expression: Application
                               └──Expression: Application
                                  └──Expression: Field
                                     └──Expression: Variable: mapper
                                     └──Label: f
                                  └──Expression: Variable: key
                               └──Expression: Variable: value
       └──Structure item: Type
          └──Type declaration:
             └──Type name: t
             └──Type parameters:
             └──Type declaration kind: Alias
                └──Type: Constructor
                   └──Constructor: list
                   └──Type: Constructor
                      └──Constructor: elem |}]

let%expect_test "top-level definition -- polymorphic recursion" =
  let str = 
    {|
      type 'a perfect_tree = 
        | Leaf of 'a
        | Node of 'a * ('a * 'a) perfect_tree
      ;;

      let rec (type 'a) length = fun (t : 'a perfect_tree) ->
        (match t with 
          ( Leaf _ -> 1
          | Node (_, t) -> 1 + 2 * (length t)
          ) 
        : int)
      ;;
    |}
  in
  print_structure_parsetree str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: perfect_tree
             └──Type parameters: a
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Leaf
                   └──Constructor argument:
                      └──Constructor existentials:
                      └──Type: Variable
                         └──Variable: a
                └──Constructor declaration:
                   └──Constructor name: Node
                   └──Constructor argument:
                      └──Constructor existentials:
                      └──Type: Tuple
                         └──Type: Variable
                            └──Variable: a
                         └──Type: Constructor
                            └──Constructor: perfect_tree
                            └──Type: Tuple
                               └──Type: Variable
                                  └──Variable: a
                               └──Type: Variable
                                  └──Variable: a
       └──Structure item: Let: Recursive
          └──Value bindings:
             └──Value binding:
                └──Pattern: Variable: length
                └──Expression: Function
                   └──Pattern: Constraint
                      └──Pattern: Variable: t
                      └──Type: Constructor
                         └──Constructor: perfect_tree
                         └──Type: Variable
                            └──Variable: a
                   └──Expression: Constraint
                      └──Expression: Match
                         └──Expression: Variable: t
                         └──Cases:
                            └──Case:
                               └──Pattern: Construct
                                  └──Constructor: Leaf
                                  └──Pattern: Any
                               └──Expression: Constant: 1
                            └──Case:
                               └──Pattern: Construct
                                  └──Constructor: Node
                                  └──Pattern: Tuple
                                     └──Pattern: Any
                                     └──Pattern: Variable: t
                               └──Expression: Application
                                  └──Expression: Application
                                     └──Expression: Primitive: (+)
                                     └──Expression: Constant: 1
                                  └──Expression: Application
                                     └──Expression: Application
                                        └──Expression: Primitive: (*)
                                        └──Expression: Constant: 2
                                     └──Expression: Application
                                        └──Expression: Variable: length
                                        └──Expression: Variable: t
                      └──Type: Constructor
                         └──Constructor: int |}]

let%expect_test "eval example" =
  let str = 
    {|
      type bin_op = Add | Sub;;

      type expr = 
        | Int of int
        | Var of string
        | Let of binding list * expr
        | Bin_op of expr * bin_op * expr
      and binding = 
        { var : string
        ; exp : expr
        }
      ;;

      let eval_bin_op = fun op n1 n2 -> 
        match op with
        ( Add -> n1 + n2
        | Sub -> n1 - n2
        )
      ;;

      let rec eval = fun env exp ->
        match exp with
        ( Int n -> n
        | Var x -> env_find env x
        | Let (bindings, in_) -> 
          let env = bind env bindings in
          eval env in_
        | Bin_op (left, op, right) ->
          let n1 = eval env left 
          and n2 = eval env right in
          eval_bin_op op n1 n2
        )
      and bind = fun env bindings -> 
        fold_right bindings env (fun binding env ->
          env_bind env binding.var binding.exp)
      ;;
    |}
  in
  print_structure_parsetree str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: bin_op
             └──Type parameters:
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Add
                └──Constructor declaration:
                   └──Constructor name: Sub
       └──Structure item: Type
          └──Type declaration:
             └──Type name: expr
             └──Type parameters:
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Int
                   └──Constructor argument:
                      └──Constructor existentials:
                      └──Type: Constructor
                         └──Constructor: int
                └──Constructor declaration:
                   └──Constructor name: Var
                   └──Constructor argument:
                      └──Constructor existentials:
                      └──Type: Constructor
                         └──Constructor: string
                └──Constructor declaration:
                   └──Constructor name: Let
                   └──Constructor argument:
                      └──Constructor existentials:
                      └──Type: Tuple
                         └──Type: Constructor
                            └──Constructor: list
                            └──Type: Constructor
                               └──Constructor: binding
                         └──Type: Constructor
                            └──Constructor: expr
                └──Constructor declaration:
                   └──Constructor name: Bin_op
                   └──Constructor argument:
                      └──Constructor existentials:
                      └──Type: Tuple
                         └──Type: Constructor
                            └──Constructor: expr
                         └──Type: Constructor
                            └──Constructor: bin_op
                         └──Type: Constructor
                            └──Constructor: expr
          └──Type declaration:
             └──Type name: binding
             └──Type parameters:
             └──Type declaration kind: Record
                └──Label declaration:
                   └──Label name: var
                   └──Label polymorphic parameters:
                   └──Type: Constructor
                      └──Constructor: string
                └──Label declaration:
                   └──Label name: exp
                   └──Label polymorphic parameters:
                   └──Type: Constructor
                      └──Constructor: expr
       └──Structure item: Let: Nonrecursive
          └──Value bindings:
             └──Value binding:
                └──Pattern: Variable: eval_bin_op
                └──Expression: Function
                   └──Pattern: Variable: op
                   └──Expression: Function
                      └──Pattern: Variable: n1
                      └──Expression: Function
                         └──Pattern: Variable: n2
                         └──Expression: Match
                            └──Expression: Variable: op
                            └──Cases:
                               └──Case:
                                  └──Pattern: Construct
                                     └──Constructor: Add
                                  └──Expression: Application
                                     └──Expression: Application
                                        └──Expression: Primitive: (+)
                                        └──Expression: Variable: n1
                                     └──Expression: Variable: n2
                               └──Case:
                                  └──Pattern: Construct
                                     └──Constructor: Sub
                                  └──Expression: Application
                                     └──Expression: Application
                                        └──Expression: Primitive: (-)
                                        └──Expression: Variable: n1
                                     └──Expression: Variable: n2
       └──Structure item: Let: Recursive
          └──Value bindings:
             └──Value binding:
                └──Pattern: Variable: eval
                └──Expression: Function
                   └──Pattern: Variable: env
                   └──Expression: Function
                      └──Pattern: Variable: exp
                      └──Expression: Match
                         └──Expression: Variable: exp
                         └──Cases:
                            └──Case:
                               └──Pattern: Construct
                                  └──Constructor: Int
                                  └──Pattern: Variable: n
                               └──Expression: Variable: n
                            └──Case:
                               └──Pattern: Construct
                                  └──Constructor: Var
                                  └──Pattern: Variable: x
                               └──Expression: Application
                                  └──Expression: Application
                                     └──Expression: Variable: env_find
                                     └──Expression: Variable: env
                                  └──Expression: Variable: x
                            └──Case:
                               └──Pattern: Construct
                                  └──Constructor: Let
                                  └──Pattern: Tuple
                                     └──Pattern: Variable: bindings
                                     └──Pattern: Variable: in_
                               └──Expression: Let: Nonrecursive
                                  └──Value bindings:
                                     └──Value binding:
                                        └──Pattern: Variable: env
                                        └──Expression: Application
                                           └──Expression: Application
                                              └──Expression: Variable: bind
                                              └──Expression: Variable: env
                                           └──Expression: Variable: bindings
                                  └──Expression: Application
                                     └──Expression: Application
                                        └──Expression: Variable: eval
                                        └──Expression: Variable: env
                                     └──Expression: Variable: in_
                            └──Case:
                               └──Pattern: Construct
                                  └──Constructor: Bin_op
                                  └──Pattern: Tuple
                                     └──Pattern: Variable: left
                                     └──Pattern: Variable: op
                                     └──Pattern: Variable: right
                               └──Expression: Let: Nonrecursive
                                  └──Value bindings:
                                     └──Value binding:
                                        └──Pattern: Variable: n1
                                        └──Expression: Application
                                           └──Expression: Application
                                              └──Expression: Variable: eval
                                              └──Expression: Variable: env
                                           └──Expression: Variable: left
                                     └──Value binding:
                                        └──Pattern: Variable: n2
                                        └──Expression: Application
                                           └──Expression: Application
                                              └──Expression: Variable: eval
                                              └──Expression: Variable: env
                                           └──Expression: Variable: right
                                  └──Expression: Application
                                     └──Expression: Application
                                        └──Expression: Application
                                           └──Expression: Variable: eval_bin_op
                                           └──Expression: Variable: op
                                        └──Expression: Variable: n1
                                     └──Expression: Variable: n2
             └──Value binding:
                └──Pattern: Variable: bind
                └──Expression: Function
                   └──Pattern: Variable: env
                   └──Expression: Function
                      └──Pattern: Variable: bindings
                      └──Expression: Application
                         └──Expression: Application
                            └──Expression: Application
                               └──Expression: Variable: fold_right
                               └──Expression: Variable: bindings
                            └──Expression: Variable: env
                         └──Expression: Function
                            └──Pattern: Variable: binding
                            └──Expression: Function
                               └──Pattern: Variable: env
                               └──Expression: Application
                                  └──Expression: Application
                                     └──Expression: Application
                                        └──Expression: Variable: env_bind
                                        └──Expression: Variable: env
                                     └──Expression: Field
                                        └──Expression: Variable: binding
                                        └──Label: var
                                  └──Expression: Field
                                     └──Expression: Variable: binding
                                     └──Label: exp |}]

let%expect_test "exceptions - no argument" =
  let str = 
    {|
      exception Not_found;;

      let rec find = fun t p ->
        match t with
        ( Nil -> raise Not_found
        | Cons (x, t) -> if p x then x else find t p
        )
      ;;
    |}
  in
  print_structure_parsetree str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Exception
          └──Type exception:
             └──Extension constructor:
                └──Extension constructor kind: Declaration
                   └──Constructor declaration:
                      └──Constructor name: Not_found
       └──Structure item: Let: Recursive
          └──Value bindings:
             └──Value binding:
                └──Pattern: Variable: find
                └──Expression: Function
                   └──Pattern: Variable: t
                   └──Expression: Function
                      └──Pattern: Variable: p
                      └──Expression: Match
                         └──Expression: Variable: t
                         └──Cases:
                            └──Case:
                               └──Pattern: Construct
                                  └──Constructor: Nil
                               └──Expression: Application
                                  └──Expression: Variable: raise
                                  └──Expression: Construct
                                     └──Constructor: Not_found
                            └──Case:
                               └──Pattern: Construct
                                  └──Constructor: Cons
                                  └──Pattern: Tuple
                                     └──Pattern: Variable: x
                                     └──Pattern: Variable: t
                               └──Expression: If
                                  └──Expression: Application
                                     └──Expression: Variable: p
                                     └──Expression: Variable: x
                                  └──Expression: Variable: x
                                  └──Expression: Application
                                     └──Expression: Application
                                        └──Expression: Variable: find
                                        └──Expression: Variable: t
                                     └──Expression: Variable: p |}]

let%expect_test "exceptions - argument" =
  let str = 
    {|
      exception Lexer_error of string;;

      let lex_eof = fun token -> 
        match token with
        ( Eof -> ()
        | _ -> raise (Lexer_error "Unexpected token!")
        )
      ;;
    |}
  in
  print_structure_parsetree str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Exception
          └──Type exception:
             └──Extension constructor:
                └──Extension constructor kind: Declaration
                   └──Constructor declaration:
                      └──Constructor name: Lexer_error
                      └──Constructor argument:
                         └──Constructor existentials:
                         └──Type: Constructor
                            └──Constructor: string
       └──Structure item: Let: Nonrecursive
          └──Value bindings:
             └──Value binding:
                └──Pattern: Variable: lex_eof
                └──Expression: Function
                   └──Pattern: Variable: token
                   └──Expression: Match
                      └──Expression: Variable: token
                      └──Cases:
                         └──Case:
                            └──Pattern: Construct
                               └──Constructor: Eof
                            └──Expression: Constant: ()
                         └──Case:
                            └──Pattern: Any
                            └──Expression: Application
                               └──Expression: Variable: raise
                               └──Expression: Construct
                                  └──Constructor: Lexer_error
                                  └──Expression: Constant: Unexpected token! |}]

let%expect_test "top level external definitions" =
  let str = 
    {|
      external greater_than : int -> int -> bool = "%greater_than";;

      external to_sexp : 'a. 'a -> sexp = "%to_sexp";;

      external print_endline : string -> unit = "%print_endline";;

      let () = print_endline "Hello world!";;
    |}
  in
  print_structure_parsetree str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Primitive
          └──Value description:
             └──Name: greater_than
             └──Scheme:
                └──Variables: []
                └──Type: Arrow
                   └──Type: Constructor
                      └──Constructor: int
                   └──Type: Arrow
                      └──Type: Constructor
                         └──Constructor: int
                      └──Type: Constructor
                         └──Constructor: bool
             └──Primitive name: %greater_than
       └──Structure item: Primitive
          └──Value description:
             └──Name: to_sexp
             └──Scheme:
                └──Variables: a
                └──Type: Arrow
                   └──Type: Variable
                      └──Variable: a
                   └──Type: Constructor
                      └──Constructor: sexp
             └──Primitive name: %to_sexp
       └──Structure item: Primitive
          └──Value description:
             └──Name: print_endline
             └──Scheme:
                └──Variables: []
                └──Type: Arrow
                   └──Type: Constructor
                      └──Constructor: string
                   └──Type: Constructor
                      └──Constructor: unit
             └──Primitive name: %print_endline
       └──Structure item: Let: Nonrecursive
          └──Value bindings:
             └──Value binding:
                └──Pattern: Constant: ()
                └──Expression: Application
                   └──Expression: Variable: print_endline
                   └──Expression: Constant: Hello world! |}]

let%expect_test "type definition - abstract types" =
  let str = 
    {|
      type zero;;
      type 'n succ;;

      type ('a, 'n) list = 
        | Nil constraint 'n = zero
        | Cons of 'm. 'a * ('a, 'm) list constraint 'n = 'm succ
      ;;
    |}
  in
  print_structure_parsetree str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: zero
             └──Type parameters:
             └──Type declaration kind: Abstract
       └──Structure item: Type
          └──Type declaration:
             └──Type name: succ
             └──Type parameters: n
             └──Type declaration kind: Abstract
       └──Structure item: Type
          └──Type declaration:
             └──Type name: list
             └──Type parameters: a n
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constraint:
                      └──Type: Variable
                         └──Variable: n
                      └──Type: Constructor
                         └──Constructor: zero
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor argument:
                      └──Constructor existentials: m
                      └──Type: Tuple
                         └──Type: Variable
                            └──Variable: a
                         └──Type: Constructor
                            └──Constructor: list
                            └──Type: Variable
                               └──Variable: a
                            └──Type: Variable
                               └──Variable: m
                   └──Constraint:
                      └──Type: Variable
                         └──Variable: n
                      └──Type: Constructor
                         └──Constructor: succ
                         └──Type: Variable
                            └──Variable: m |}]

let%expect_test "where" =
  let str = 
    {|
      external length : 'a. ('c -> int) where 'c = 'a list = "%length";;
    |}
  in
  print_structure_parsetree str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Primitive
          └──Value description:
             └──Name: length
             └──Scheme:
                └──Variables: a
                └──Type: Where
                   └──Variable: c
                   └──Type: Constructor
                      └──Constructor: list
                      └──Type: Variable
                         └──Variable: a
                   └──Type: Arrow
                      └──Type: Variable
                         └──Variable: c
                      └──Type: Constructor
                         └──Constructor: int
             └──Primitive name: %length |}]