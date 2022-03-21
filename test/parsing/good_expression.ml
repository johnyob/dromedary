open! Import
open Util

let%expect_test "variable : alphas" =
  let exp = {|
      hello_world_var
    |} in
  print_expression_parsetree exp;
  [%expect {|
    Expression:
    └──Expression: Variable: hello_world_var |}]

let%expect_test "variable : alphanum" =
  let exp = {|
      hello_world_var_123
    |} in
  print_expression_parsetree exp;
  [%expect
    {|
    Expression:
    └──Expression: Variable: hello_world_var_123 |}]

let%expect_test "variable : prime" =
  let exp = {|
      x'
    |} in
  print_expression_parsetree exp;
  [%expect {|
    Expression:
    └──Expression: Variable: x' |}]

let%expect_test "constructor : alpha" =
  let exp = {|
      Nil
    |} in
  print_expression_parsetree exp;
  [%expect
    {|
    Expression:
    └──Expression: Construct
       └──Constructor: Nil |}]

let%expect_test "constructor : all" =
  let exp = {|
      True_false_11'
    |} in
  print_expression_parsetree exp;
  [%expect
    {|
    Expression:
    └──Expression: Construct
       └──Constructor: True_false_11' |}]

let%expect_test "constant : unit" =
  let exp = {| () |} in
  print_expression_parsetree exp;
  [%expect {|
    Expression:
    └──Expression: Constant: () |}]

let%expect_test "constant : int" =
  let exp = {| 5000 |} in
  print_expression_parsetree exp;
  [%expect {|
    Expression:
    └──Expression: Constant: 5000 |}]

let%expect_test "constant : int (prefixed)" =
  let exp = {|
      -10
    |} in
  print_expression_parsetree exp;
  [%expect {|
    Expression:
    └──Expression: Constant: -10 |}]

let%expect_test "constant : bool" =
  let exp = {| false |} in
  print_expression_parsetree exp;
  [%expect {|
    Expression:
    └──Expression: Constant: false |}]

let%expect_test "constant : float" =
  let exp = {|
      1234.5678
    |} in
  print_expression_parsetree exp;
  [%expect {|
    Expression:
    └──Expression: Constant: 1234.567800 |}]

let%expect_test "constant : float (prefixed)" =
  let exp = {|
      -1234.3
    |} in
  print_expression_parsetree exp;
  [%expect {|
    Expression:
    └──Expression: Constant: -1234.300000 |}]

let%expect_test "constant : float (no int part)" =
  let exp = {|
      .5
    |} in
  print_expression_parsetree exp;
  [%expect {|
    Expression:
    └──Expression: Constant: 0.500000 |}]

let%expect_test "constant : float (no frac part)" =
  let exp = {|
      3.
    |} in
  print_expression_parsetree exp;
  [%expect {|
    Expression:
    └──Expression: Constant: 3.000000 |}]

let%expect_test "constant : string (escaping)" =
  let exp = {|
      "\tHello world!\n"
    |} in
  print_expression_parsetree exp;
  [%expect {|
    Expression:
    └──Expression: Constant: 	Hello world! |}]

let%expect_test "constant : char " =
  let exp = {|
      'h'
    |} in
  print_expression_parsetree exp;
  [%expect {|
    Expression:
    └──Expression: Constant: h |}]

let%expect_test "constant : char (escaping)" =
  let exp = {|
      '\t'
    |} in
  print_expression_parsetree exp;
  [%expect {|
    Expression:
    └──Expression: Constant: |}]

let%expect_test "primitive : binary operators" =
  let exp = {| (5 + 4 - 8 * 2) / 2 = 0 |} in
  print_expression_parsetree exp;
  [%expect
    {|
    Expression:
    └──Expression: Application
       └──Expression: Application
          └──Expression: Primitive: (=)
          └──Expression: Application
             └──Expression: Application
                └──Expression: Primitive: (/)
                └──Expression: Application
                   └──Expression: Application
                      └──Expression: Primitive: (-)
                      └──Expression: Application
                         └──Expression: Application
                            └──Expression: Primitive: (+)
                            └──Expression: Constant: 5
                         └──Expression: Constant: 4
                   └──Expression: Application
                      └──Expression: Application
                         └──Expression: Primitive: (*)
                         └──Expression: Constant: 8
                      └──Expression: Constant: 2
             └──Expression: Constant: 2
       └──Expression: Constant: 0 |}]

let%expect_test "primitive : references" =
  let exp = {| ref !x := 40 + 10 |} in
  print_expression_parsetree exp;
  [%expect
    {|
    Expression:
    └──Expression: Application
       └──Expression: Application
          └──Expression: Primitive: (:=)
          └──Expression: Application
             └──Expression: Primitive: ref
             └──Expression: Application
                └──Expression: Primitive: (!)
                └──Expression: Variable: x
       └──Expression: Application
          └──Expression: Application
             └──Expression: Primitive: (+)
             └──Expression: Constant: 40
          └──Expression: Constant: 10 |}]

let%expect_test "core_type : type var" =
  let exp = {| (x : 'a) |} in
  print_expression_parsetree exp;
  [%expect
    {|
     Expression:
     └──Expression: Constraint
        └──Expression: Variable: x
        └──Type: Variable
           └──Variable: a |}]

let%expect_test "core_type : function" =
  let exp = {| (fun x -> x : (int -> int) -> int -> int) |} in
  print_expression_parsetree exp;
  [%expect
    {|
     Expression:
     └──Expression: Constraint
        └──Expression: Function
           └──Pattern: Variable: x
           └──Expression: Variable: x
        └──Type: Arrow
           └──Type: Arrow
              └──Type: Constructor
                 └──Constructor: int
              └──Type: Constructor
                 └──Constructor: int
           └──Type: Arrow
              └──Type: Constructor
                 └──Constructor: int
              └──Type: Constructor
                 └──Constructor: int |}]

let%expect_test "core_type : tuple" =
  let exp = {| ((1,2,3) : int * int * int) |} in
  print_expression_parsetree exp;
  [%expect
    {|
     Expression:
     └──Expression: Constraint
        └──Expression: Tuple
           └──Expression: Constant: 1
           └──Expression: Constant: 2
           └──Expression: Constant: 3
        └──Type: Tuple
           └──Type: Constructor
              └──Constructor: int
           └──Type: Constructor
              └──Constructor: int
           └──Type: Constructor
              └──Constructor: int |}]

let%expect_test "core_type : constr" =
  let exp = {| (Cons ((1, x), Cons ((2, y), Nil)) : (int * 'a) list) |} in
  print_expression_parsetree exp;
  [%expect
    {|
     Expression:
     └──Expression: Constraint
        └──Expression: Construct
           └──Constructor: Cons
           └──Expression: Tuple
              └──Expression: Tuple
                 └──Expression: Constant: 1
                 └──Expression: Variable: x
              └──Expression: Construct
                 └──Constructor: Cons
                 └──Expression: Tuple
                    └──Expression: Tuple
                       └──Expression: Constant: 2
                       └──Expression: Variable: y
                    └──Expression: Construct
                       └──Constructor: Nil
        └──Type: Constructor
           └──Constructor: list
           └──Type: Tuple
              └──Type: Constructor
                 └──Constructor: int
              └──Type: Variable
                 └──Variable: a |}]

let%expect_test "if" =
  let exp = {|
      if true then 3 else 4
    |} in
  print_expression_parsetree exp;
  [%expect
    {|
    Expression:
    └──Expression: If
       └──Expression: Constant: true
       └──Expression: Constant: 3
       └──Expression: Constant: 4 |}]

let%expect_test "fun : identity" =
  let exp = {| fun x -> x |} in
  print_expression_parsetree exp;
  [%expect
    {|
    Expression:
    └──Expression: Function
       └──Pattern: Variable: x
       └──Expression: Variable: x |}]

let%expect_test "fun : fst" =
  let exp = {| fun (x, y) -> x |} in
  print_expression_parsetree exp;
  [%expect
    {|
    Expression:
    └──Expression: Function
       └──Pattern: Tuple
          └──Pattern: Variable: x
          └──Pattern: Variable: y
       └──Expression: Variable: x |}]

let%expect_test "fun : map" =
  let exp =
    {|  let rec map = fun t f -> 
          match t with 
            ( Nil -> Nil
            | Cons -> Cons (f x, map t f) )
        in ()
    |}
  in
  print_expression_parsetree exp;
  [%expect
    {|
    Expression:
    └──Expression: Let: Recursive
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
       └──Expression: Constant: () |}]

let%expect_test "annotation : exists" =
  let exp =
    {| exists (type 'a 'b) -> 
        fun (x : 'a) -> (x : 'b)
    |}
  in
  print_expression_parsetree exp;
  [%expect
    {|
    Expression:
    └──Expression: Exists
       └──Variables: a,b
       └──Expression: Function
          └──Pattern: Constraint
             └──Pattern: Variable: x
             └──Type: Variable
                └──Variable: a
          └──Expression: Constraint
             └──Expression: Variable: x
             └──Type: Variable
                └──Variable: b |}]

let%expect_test "annotation : forall" =
  let exp = {| forall (type 'a) -> fun (x : 'a) -> (x : 'a) |} in
  print_expression_parsetree exp;
  [%expect
    {|
    Expression:
    └──Expression: Forall
       └──Variables: a
       └──Expression: Function
          └──Pattern: Constraint
             └──Pattern: Variable: x
             └──Type: Variable
                └──Variable: a
          └──Expression: Constraint
             └──Expression: Variable: x
             └──Type: Variable
                └──Variable: a |}]

let%expect_test "let : fact" =
  let exp =
    {| let rec fact = fun n -> 
        if n = 0 then 1 else n * fact (n - 1)
       in ()
    |}
  in
  print_expression_parsetree exp;
  [%expect
    {|
    Expression:
    └──Expression: Let: Recursive
       └──Value bindings:
          └──Value binding:
             └──Pattern: Variable: fact
             └──Expression: Function
                └──Pattern: Variable: n
                └──Expression: If
                   └──Expression: Application
                      └──Expression: Application
                         └──Expression: Primitive: (=)
                         └──Expression: Variable: n
                      └──Expression: Constant: 0
                   └──Expression: Constant: 1
                   └──Expression: Application
                      └──Expression: Application
                         └──Expression: Primitive: (*)
                         └──Expression: Variable: n
                      └──Expression: Application
                         └──Expression: Variable: fact
                         └──Expression: Application
                            └──Expression: Application
                               └──Expression: Primitive: (-)
                               └──Expression: Variable: n
                            └──Expression: Constant: 1
       └──Expression: Constant: () |}]

let%expect_test "record" =
  let exp = {| { part = Part_ii ; courses = Cons (Types, Nil) } |} in
  print_expression_parsetree exp;
  [%expect
    {|
    Expression:
    └──Expression: Record
       └──Label: part
          └──Expression: Construct
             └──Constructor: Part_ii
       └──Label: courses
          └──Expression: Construct
             └──Constructor: Cons
             └──Expression: Tuple
                └──Expression: Construct
                   └──Constructor: Types
                └──Expression: Construct
                   └──Constructor: Nil |}]

let%expect_test "field" =
  let exp = {| let name_of_student = fun t -> t.name in () |} in
  print_expression_parsetree exp;
  [%expect
    {|
    Expression:
    └──Expression: Let: Nonrecursive
       └──Value bindings:
          └──Value binding:
             └──Pattern: Variable: name_of_student
             └──Expression: Function
                └──Pattern: Variable: t
                └──Expression: Field
                   └──Expression: Variable: t
                   └──Label: name
       └──Expression: Constant: () |}]

let%expect_test "tuples" =
  let exp = {| (1, 2, 3, (5, 6, 7), (), ((1,2,3))) |} in
  print_expression_parsetree exp;
  [%expect
    {|
    Expression:
    └──Expression: Tuple
       └──Expression: Constant: 1
       └──Expression: Constant: 2
       └──Expression: Constant: 3
       └──Expression: Tuple
          └──Expression: Constant: 5
          └──Expression: Constant: 6
          └──Expression: Constant: 7
       └──Expression: Constant: ()
       └──Expression: Tuple
          └──Expression: Constant: 1
          └──Expression: Constant: 2
          └──Expression: Constant: 3 |}]

let%expect_test "function - uncurry" =
  let exp = {| fun f (x, y) -> f x y |} in
  print_expression_parsetree exp;
  [%expect
    {|
    Expression:
    └──Expression: Function
       └──Pattern: Variable: f
       └──Expression: Function
          └──Pattern: Tuple
             └──Pattern: Variable: x
             └──Pattern: Variable: y
          └──Expression: Application
             └──Expression: Application
                └──Expression: Variable: f
                └──Expression: Variable: x
             └──Expression: Variable: y |}]

let%expect_test "let-and" =
  let exp = {| 
    let x = 1
    and y = 2
    in x + y
  |} in
  print_expression_parsetree exp;
  [%expect
    {|
    Expression:
    └──Expression: Let: Nonrecursive
       └──Value bindings:
          └──Value binding:
             └──Pattern: Variable: x
             └──Expression: Constant: 1
          └──Value binding:
             └──Pattern: Variable: y
             └──Expression: Constant: 2
       └──Expression: Application
          └──Expression: Application
             └──Expression: Primitive: (+)
             └──Expression: Variable: x
          └──Expression: Variable: y |}]

let%expect_test "function : is_even" =
  let exp =
    {| 
      let rec is_even = fun n ->
        if n = 0 then true else is_odd (n - 1)
      and is_odd = fun n ->
        if n = 1 then true else is_even (n - 1)
      in is_even 1
    |}
  in
  print_expression_parsetree exp;
  [%expect
    {|
    Expression:
    └──Expression: Let: Recursive
       └──Value bindings:
          └──Value binding:
             └──Pattern: Variable: is_even
             └──Expression: Function
                └──Pattern: Variable: n
                └──Expression: If
                   └──Expression: Application
                      └──Expression: Application
                         └──Expression: Primitive: (=)
                         └──Expression: Variable: n
                      └──Expression: Constant: 0
                   └──Expression: Constant: true
                   └──Expression: Application
                      └──Expression: Variable: is_odd
                      └──Expression: Application
                         └──Expression: Application
                            └──Expression: Primitive: (-)
                            └──Expression: Variable: n
                         └──Expression: Constant: 1
          └──Value binding:
             └──Pattern: Variable: is_odd
             └──Expression: Function
                └──Pattern: Variable: n
                └──Expression: If
                   └──Expression: Application
                      └──Expression: Application
                         └──Expression: Primitive: (=)
                         └──Expression: Variable: n
                      └──Expression: Constant: 1
                   └──Expression: Constant: true
                   └──Expression: Application
                      └──Expression: Variable: is_even
                      └──Expression: Application
                         └──Expression: Application
                            └──Expression: Primitive: (-)
                            └──Expression: Variable: n
                         └──Expression: Constant: 1
       └──Expression: Application
          └──Expression: Variable: is_even
          └──Expression: Constant: 1 |}]

let%expect_test "try" =
  let exp =
    {| 
      let rec find_exn = fun t f ->
        match t with
        ( Nil -> raise Not_found
        | Cons (x, t) -> if f x then x else find_exn t f)
      in ()  
    |}
  in
  print_expression_parsetree exp;
  [%expect
    {|
    Expression:
    └──Expression: Let: Recursive
       └──Value bindings:
          └──Value binding:
             └──Pattern: Variable: find_exn
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
                                  └──Expression: Variable: f
                                  └──Expression: Variable: x
                               └──Expression: Variable: x
                               └──Expression: Application
                                  └──Expression: Application
                                     └──Expression: Variable: find_exn
                                     └──Expression: Variable: t
                                  └──Expression: Variable: f
       └──Expression: Constant: () |}]

let%expect_test "fact : while" =
  let exp =
    {| 
      let fact = fun n ->
        let i = ref n in
        let result = ref 1 in
        while ge i 0 do
          result := !result * !i;
          i := !i - 1         
        done;
        !result
      in ()
    |}
  in
  print_expression_parsetree exp;
  [%expect
    {|
    Expression:
    └──Expression: Let: Nonrecursive
       └──Value bindings:
          └──Value binding:
             └──Pattern: Variable: fact
             └──Expression: Function
                └──Pattern: Variable: n
                └──Expression: Let: Nonrecursive
                   └──Value bindings:
                      └──Value binding:
                         └──Pattern: Variable: i
                         └──Expression: Application
                            └──Expression: Primitive: ref
                            └──Expression: Variable: n
                   └──Expression: Let: Nonrecursive
                      └──Value bindings:
                         └──Value binding:
                            └──Pattern: Variable: result
                            └──Expression: Application
                               └──Expression: Primitive: ref
                               └──Expression: Constant: 1
                      └──Expression: Sequence
                         └──Expression: While
                            └──Expression: Application
                               └──Expression: Application
                                  └──Expression: Variable: ge
                                  └──Expression: Variable: i
                               └──Expression: Constant: 0
                            └──Expression: Sequence
                               └──Expression: Application
                                  └──Expression: Application
                                     └──Expression: Primitive: (:=)
                                     └──Expression: Variable: result
                                  └──Expression: Application
                                     └──Expression: Application
                                        └──Expression: Primitive: (*)
                                        └──Expression: Application
                                           └──Expression: Primitive: (!)
                                           └──Expression: Variable: result
                                     └──Expression: Application
                                        └──Expression: Primitive: (!)
                                        └──Expression: Variable: i
                               └──Expression: Application
                                  └──Expression: Application
                                     └──Expression: Primitive: (:=)
                                     └──Expression: Variable: i
                                  └──Expression: Application
                                     └──Expression: Application
                                        └──Expression: Primitive: (-)
                                        └──Expression: Application
                                           └──Expression: Primitive: (!)
                                           └──Expression: Variable: i
                                     └──Expression: Constant: 1
                         └──Expression: Application
                            └──Expression: Primitive: (!)
                            └──Expression: Variable: result
       └──Expression: Constant: () |}]

let%expect_test "fact : for" =
  let exp =
    {|
      let fact = fun n ->
        let result = ref 1 in
        for i = 1 to n do
          result := !result * i
        done;
        !result
      in ()
    |}
  in
  print_expression_parsetree exp;
  [%expect
    {|
    Expression:
    └──Expression: Let: Nonrecursive
       └──Value bindings:
          └──Value binding:
             └──Pattern: Variable: fact
             └──Expression: Function
                └──Pattern: Variable: n
                └──Expression: Let: Nonrecursive
                   └──Value bindings:
                      └──Value binding:
                         └──Pattern: Variable: result
                         └──Expression: Application
                            └──Expression: Primitive: ref
                            └──Expression: Constant: 1
                   └──Expression: Sequence
                      └──Expression: For
                         └──Pattern: Variable: i
                         └──Expression: Constant: 1
                         └──Direction: to
                         └──Expression: Variable: n
                         └──Expression: Application
                            └──Expression: Application
                               └──Expression: Primitive: (:=)
                               └──Expression: Variable: result
                            └──Expression: Application
                               └──Expression: Application
                                  └──Expression: Primitive: (*)
                                  └──Expression: Application
                                     └──Expression: Primitive: (!)
                                     └──Expression: Variable: result
                               └──Expression: Variable: i
                      └──Expression: Application
                         └──Expression: Primitive: (!)
                         └──Expression: Variable: result
       └──Expression: Constant: () |}]

let%expect_test "pattern : constant" =
  let exp = {|
      fun 1 -> ()
    |} in
  print_expression_parsetree exp;
  [%expect {|
    Expression:
    └──Expression: Function
       └──Pattern: Constant: 1
       └──Expression: Constant: () |}]

let%expect_test "pattern : wildcard" =
  let exp = 
    {|
      fun _ -> ()
    |}
  in
  print_expression_parsetree exp;
  [%expect {|
    Expression:
    └──Expression: Function
       └──Pattern: Any
       └──Expression: Constant: () |}]

let%expect_test "pattern : constructor" =
  let exp = 
    {|
      fun (Cons (x, t)) -> x
    |}
  in
  print_expression_parsetree exp;
  [%expect {|
    Expression:
    └──Expression: Function
       └──Pattern: Construct
          └──Constructor: Cons
          └──Pattern: Tuple
             └──Pattern: Variable: x
             └──Pattern: Variable: t
       └──Expression: Variable: x |}]

let%expect_test "pattern : tuple" =
  let exp = 
    {|
      fun (x, _, _, _) -> x
    |}
  in
  print_expression_parsetree exp;
  [%expect {|
    Expression:
    └──Expression: Function
       └──Pattern: Tuple
          └──Pattern: Variable: x
          └──Pattern: Any
          └──Pattern: Any
          └──Pattern: Any
       └──Expression: Variable: x |}]

let%expect_test "pattern : annotation" =
  let exp = 
    {|
      fun (x : 'a) -> x
    |}
  in
  print_expression_parsetree exp;
  [%expect {|
    Expression:
    └──Expression: Function
       └──Pattern: Constraint
          └──Pattern: Variable: x
          └──Type: Variable
             └──Variable: a
       └──Expression: Variable: x |}]


let%expect_test "pattern : as" =
  let exp = 
    {|
      fun ((Cons (x as y, _)) as t) -> y
    |}
  in
  print_expression_parsetree exp;
  [%expect {|
    Expression:
    └──Expression: Function
       └──Pattern: Alias
          └──Pattern: Construct
             └──Constructor: Cons
             └──Pattern: Tuple
                └──Pattern: Alias
                   └──Pattern: Variable: x
                   └──As: y
                └──Pattern: Any
          └──As: t
       └──Expression: Variable: y |}]