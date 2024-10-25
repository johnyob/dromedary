open! Import
open Parsetree
open Ast_types
open Types
module Constraint = Typing.Private.Constraint
open Constraint

let print_constraint_result ~env exp =
  let t =
    Private.Infer_core.Expression.(infer_exp_ exp |> Computation.run ~env)
  in
  let output =
    match t with
    | Ok t -> Constraint.sexp_of_t t
    | Error err -> err
  in
  output |> Sexp.to_string_hum |> print_endline


let print_solve_result ?(debug = false) ?(abbrevs = Abbreviations.empty) cst =
  Constraint.sexp_of_t cst |> Sexp.to_string_hum |> print_endline;
  match Private.solve ~debug ~abbrevs cst with
  | Ok _ -> Format.fprintf Format.std_formatter "Constraint is true.\n"
  | Error err -> Sexp.to_string_hum err |> print_endline


let print_infer_result
  ~env
  ?(debug = false)
  ?(abbrevs = Abbreviations.empty)
  exp
  =
  let texp = Typing.infer_exp ~debug ~env ~abbrevs exp in
  match texp with
  | Ok (variables, texp) ->
    let ppf = Format.std_formatter in
    Format.fprintf
      ppf
      "Variables: %s@."
      (String.concat
         ~sep:","
         (List.map ~f:(fun var -> Type_var.id var |> Int.to_string) variables));
    Typedtree.pp_expression_mach ppf texp
  | Error err -> Sexp.to_string_hum err |> print_endline


let print_infer_result'
  ~env
  ?(debug = false)
  ?(abbrevs = Abbreviations.empty)
  exp
  =
  match Parsing.parse_expression_from_string exp with
  | Ok exp -> print_infer_result ~env ~debug ~abbrevs exp
  | Error err ->
    (match err with
     | `Lexer_error message -> [%sexp ("lexer error: " ^ message : string)]
     | `Parser_error -> [%sexp ("parse error" : string)])
    |> Sexp.to_string_hum
    |> print_endline


let add_list env =
  let name = "list" in
  let a = Type_var.make () in
  let params = [ a ] in
  let a' = Type_expr.make (Ttyp_var a) in
  let type_ = Type_expr.make (Ttyp_constr ([ a' ], name)) in
  Env.add_type_decl
    env
    { type_name = name
    ; type_kind =
        Type_variant
          [ { constructor_name = "Nil"
            ; constructor_alphas = params
            ; constructor_arg = None
            ; constructor_type = type_
            ; constructor_constraints = []
            }
          ; { constructor_name = "Cons"
            ; constructor_alphas = params
            ; constructor_arg =
                Some
                  { constructor_arg_betas = []
                  ; constructor_arg_type =
                      Type_expr.make (Ttyp_tuple [ a'; type_ ])
                  }
            ; constructor_type = type_
            ; constructor_constraints = []
            }
          ]
    }


let%expect_test "constant: int" =
  let exp = Pexp_const (Const_int 1) in
  print_infer_result ~env:Env.empty exp;
  [%expect
    {|
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Constructor: int
       └──Desc: Constant: 1 |}]


let%expect_test "constant: bool" =
  let exp = Pexp_const (Const_bool true) in
  print_infer_result ~env:Env.empty exp;
  [%expect
    {|
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Constructor: bool
       └──Desc: Constant: true |}]


let%expect_test "constant: unit" =
  let exp = Pexp_const Const_unit in
  print_infer_result ~env:Env.empty exp;
  [%expect
    {|
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Constructor: unit
       └──Desc: Constant: () |}]


let%expect_test "primitives" =
  let exp =
    (* (1 + (2 / 1 - 0 * 1)) = 12 *)
    let lhs =
      let rhs =
        let lhs =
          Pexp_app
            ( Pexp_app (Pexp_prim Prim_div, Pexp_const (Const_int 2))
            , Pexp_const (Const_int 1) )
        in
        let rhs =
          Pexp_app
            ( Pexp_app (Pexp_prim Prim_mul, Pexp_const (Const_int 0))
            , Pexp_const (Const_int 1) )
        in
        Pexp_app (Pexp_app (Pexp_prim Prim_sub, lhs), rhs)
      in
      Pexp_app (Pexp_app (Pexp_prim Prim_add, Pexp_const (Const_int 1)), rhs)
    in
    Pexp_app (Pexp_app (Pexp_prim Prim_eq, lhs), Pexp_const (Const_int 12))
  in
  print_infer_result ~env:Env.empty exp;
  [%expect
    {|
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Constructor: bool
       └──Desc: Application
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Constructor: int
                └──Type expr: Constructor: bool
             └──Desc: Application
                └──Expression:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: int
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: bool
                   └──Desc: Primitive: (=)
                └──Expression:
                   └──Type expr: Constructor: int
                   └──Desc: Application
                      └──Expression:
                         └──Type expr: Arrow
                            └──Type expr: Constructor: int
                            └──Type expr: Constructor: int
                         └──Desc: Application
                            └──Expression:
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: int
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: int
                               └──Desc: Primitive: (+)
                            └──Expression:
                               └──Type expr: Constructor: int
                               └──Desc: Constant: 1
                      └──Expression:
                         └──Type expr: Constructor: int
                         └──Desc: Application
                            └──Expression:
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: int
                                  └──Type expr: Constructor: int
                               └──Desc: Application
                                  └──Expression:
                                     └──Type expr: Arrow
                                        └──Type expr: Constructor: int
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: int
                                           └──Type expr: Constructor: int
                                     └──Desc: Primitive: (-)
                                  └──Expression:
                                     └──Type expr: Constructor: int
                                     └──Desc: Application
                                        └──Expression:
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: int
                                              └──Type expr: Constructor: int
                                           └──Desc: Application
                                              └──Expression:
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: int
                                                       └──Type expr: Constructor: int
                                                 └──Desc: Primitive: (/)
                                              └──Expression:
                                                 └──Type expr: Constructor: int
                                                 └──Desc: Constant: 2
                                        └──Expression:
                                           └──Type expr: Constructor: int
                                           └──Desc: Constant: 1
                            └──Expression:
                               └──Type expr: Constructor: int
                               └──Desc: Application
                                  └──Expression:
                                     └──Type expr: Arrow
                                        └──Type expr: Constructor: int
                                        └──Type expr: Constructor: int
                                     └──Desc: Application
                                        └──Expression:
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: int
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                           └──Desc: Primitive: (*)
                                        └──Expression:
                                           └──Type expr: Constructor: int
                                           └──Desc: Constant: 0
                                  └──Expression:
                                     └──Type expr: Constructor: int
                                     └──Desc: Constant: 1
          └──Expression:
             └──Type expr: Constructor: int
             └──Desc: Constant: 12 |}]


let%expect_test "function - identity" =
  let exp =
    (* fun x -> x *)
    Pexp_fun (Ppat_var "x", Pexp_var "x")
  in
  print_infer_result ~env:Env.empty exp;
  [%expect
    {|
    Variables: 2,2
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Variable: 2
          └──Type expr: Variable: 2
       └──Desc: Function
          └──Pattern:
             └──Type expr: Variable: 2
             └──Desc: Variable: x
          └──Expression:
             └──Type expr: Variable: 2
             └──Desc: Variable
                └──Variable: x |}]


let%expect_test "function - curry" =
  let exp =
    (* fun f x y -> f (x, y) *)
    Pexp_fun
      ( Ppat_var "f"
      , Pexp_fun
          ( Ppat_var "x"
          , Pexp_fun
              ( Ppat_var "y"
              , Pexp_app
                  (Pexp_var "f", Pexp_tuple [ Pexp_var "x"; Pexp_var "y" ]) ) )
      )
  in
  print_infer_result ~env:Env.empty exp;
  [%expect
    {|
    Variables: 10
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Arrow
             └──Type expr: Tuple
                └──Type expr: Variable: 16
                └──Type expr: Variable: 17
             └──Type expr: Variable: 10
          └──Type expr: Arrow
             └──Type expr: Variable: 16
             └──Type expr: Arrow
                └──Type expr: Variable: 17
                └──Type expr: Variable: 10
       └──Desc: Function
          └──Pattern:
             └──Type expr: Arrow
                └──Type expr: Tuple
                   └──Type expr: Variable: 16
                   └──Type expr: Variable: 17
                └──Type expr: Variable: 10
             └──Desc: Variable: f
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Variable: 16
                └──Type expr: Arrow
                   └──Type expr: Variable: 17
                   └──Type expr: Variable: 10
             └──Desc: Function
                └──Pattern:
                   └──Type expr: Variable: 16
                   └──Desc: Variable: x
                └──Expression:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 17
                      └──Type expr: Variable: 10
                   └──Desc: Function
                      └──Pattern:
                         └──Type expr: Variable: 17
                         └──Desc: Variable: y
                      └──Expression:
                         └──Type expr: Variable: 10
                         └──Desc: Application
                            └──Expression:
                               └──Type expr: Arrow
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: 16
                                     └──Type expr: Variable: 17
                                  └──Type expr: Variable: 10
                               └──Desc: Variable
                                  └──Variable: f
                            └──Expression:
                               └──Type expr: Tuple
                                  └──Type expr: Variable: 16
                                  └──Type expr: Variable: 17
                               └──Desc: Tuple
                                  └──Expression:
                                     └──Type expr: Variable: 16
                                     └──Desc: Variable
                                        └──Variable: x
                                  └──Expression:
                                     └──Type expr: Variable: 17
                                     └──Desc: Variable
                                        └──Variable: y |}]


let%expect_test "function - uncurry" =
  let exp =
    (* fun f (x, y) -> f x y *)
    Pexp_fun
      ( Ppat_var "f"
      , Pexp_fun
          ( Ppat_tuple [ Ppat_var "x"; Ppat_var "y" ]
          , Pexp_app (Pexp_app (Pexp_var "f", Pexp_var "x"), Pexp_var "y") ) )
  in
  print_infer_result ~env:Env.empty exp;
  [%expect
    {|
    Variables: 6,16,13,13,16
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Arrow
             └──Type expr: Variable: 16
             └──Type expr: Arrow
                └──Type expr: Variable: 13
                └──Type expr: Variable: 6
          └──Type expr: Arrow
             └──Type expr: Tuple
                └──Type expr: Variable: 16
                └──Type expr: Variable: 13
             └──Type expr: Variable: 6
       └──Desc: Function
          └──Pattern:
             └──Type expr: Arrow
                └──Type expr: Variable: 16
                └──Type expr: Arrow
                   └──Type expr: Variable: 13
                   └──Type expr: Variable: 6
             └──Desc: Variable: f
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Tuple
                   └──Type expr: Variable: 16
                   └──Type expr: Variable: 13
                └──Type expr: Variable: 6
             └──Desc: Function
                └──Pattern:
                   └──Type expr: Tuple
                      └──Type expr: Variable: 16
                      └──Type expr: Variable: 13
                   └──Desc: Tuple
                      └──Pattern:
                         └──Type expr: Variable: 16
                         └──Desc: Variable: x
                      └──Pattern:
                         └──Type expr: Variable: 13
                         └──Desc: Variable: y
                └──Expression:
                   └──Type expr: Variable: 6
                   └──Desc: Application
                      └──Expression:
                         └──Type expr: Arrow
                            └──Type expr: Variable: 13
                            └──Type expr: Variable: 6
                         └──Desc: Application
                            └──Expression:
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 16
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 13
                                     └──Type expr: Variable: 6
                               └──Desc: Variable
                                  └──Variable: f
                            └──Expression:
                               └──Type expr: Variable: 16
                               └──Desc: Variable
                                  └──Variable: x
                      └──Expression:
                         └──Type expr: Variable: 13
                         └──Desc: Variable
                            └──Variable: y |}]


let%expect_test "function - compose" =
  let exp =
    (* fun f g -> fun x -> f (g x) *)
    Pexp_fun
      ( Ppat_var "f"
      , Pexp_fun
          ( Ppat_var "g"
          , Pexp_fun
              ( Ppat_var "x"
              , Pexp_app (Pexp_var "f", Pexp_app (Pexp_var "g", Pexp_var "x"))
              ) ) )
  in
  print_infer_result ~env:Env.empty exp;
  [%expect
    {|
    Variables: 10
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Arrow
             └──Type expr: Variable: 13
             └──Type expr: Variable: 10
          └──Type expr: Arrow
             └──Type expr: Arrow
                └──Type expr: Variable: 16
                └──Type expr: Variable: 13
             └──Type expr: Arrow
                └──Type expr: Variable: 16
                └──Type expr: Variable: 10
       └──Desc: Function
          └──Pattern:
             └──Type expr: Arrow
                └──Type expr: Variable: 13
                └──Type expr: Variable: 10
             └──Desc: Variable: f
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Arrow
                   └──Type expr: Variable: 16
                   └──Type expr: Variable: 13
                └──Type expr: Arrow
                   └──Type expr: Variable: 16
                   └──Type expr: Variable: 10
             └──Desc: Function
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 16
                      └──Type expr: Variable: 13
                   └──Desc: Variable: g
                └──Expression:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 16
                      └──Type expr: Variable: 10
                   └──Desc: Function
                      └──Pattern:
                         └──Type expr: Variable: 16
                         └──Desc: Variable: x
                      └──Expression:
                         └──Type expr: Variable: 10
                         └──Desc: Application
                            └──Expression:
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 13
                                  └──Type expr: Variable: 10
                               └──Desc: Variable
                                  └──Variable: f
                            └──Expression:
                               └──Type expr: Variable: 13
                               └──Desc: Application
                                  └──Expression:
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: 16
                                        └──Type expr: Variable: 13
                                     └──Desc: Variable
                                        └──Variable: g
                                  └──Expression:
                                     └──Type expr: Variable: 16
                                     └──Desc: Variable
                                        └──Variable: x |}]


let%expect_test "function - fst" =
  let exp =
    (* fun (x, y) -> x *)
    Pexp_fun (Ppat_tuple [ Ppat_var "x"; Ppat_var "y" ], Pexp_var "x")
  in
  print_infer_result ~env:Env.empty exp;
  [%expect
    {|
    Variables: 5,2,2
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Tuple
             └──Type expr: Variable: 2
             └──Type expr: Variable: 5
          └──Type expr: Variable: 2
       └──Desc: Function
          └──Pattern:
             └──Type expr: Tuple
                └──Type expr: Variable: 2
                └──Type expr: Variable: 5
             └──Desc: Tuple
                └──Pattern:
                   └──Type expr: Variable: 2
                   └──Desc: Variable: x
                └──Pattern:
                   └──Type expr: Variable: 5
                   └──Desc: Variable: y
          └──Expression:
             └──Type expr: Variable: 2
             └──Desc: Variable
                └──Variable: x |}]


let%expect_test "function - snd" =
  let exp =
    (* fun (x, y) -> y *)
    Pexp_fun (Ppat_tuple [ Ppat_var "x"; Ppat_var "y" ], Pexp_var "y")
  in
  print_infer_result ~env:Env.empty exp;
  [%expect
    {|
    Variables: 2,6,2
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Tuple
             └──Type expr: Variable: 6
             └──Type expr: Variable: 2
          └──Type expr: Variable: 2
       └──Desc: Function
          └──Pattern:
             └──Type expr: Tuple
                └──Type expr: Variable: 6
                └──Type expr: Variable: 2
             └──Desc: Tuple
                └──Pattern:
                   └──Type expr: Variable: 6
                   └──Desc: Variable: x
                └──Pattern:
                   └──Type expr: Variable: 2
                   └──Desc: Variable: y
          └──Expression:
             └──Type expr: Variable: 2
             └──Desc: Variable
                └──Variable: y |}]


let%expect_test "function - hd" =
  let env = add_list Env.empty in
  let exp =
    (* fun (Cons (x, _)) -> x *)
    Pexp_fun
      ( Ppat_construct ("Cons", Some ([], Ppat_tuple [ Ppat_var "x"; Ppat_any ]))
      , Pexp_var "x" )
  in
  print_infer_result ~env exp;
  [%expect
    {|
    Variables: 2,2
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Constructor: list
             └──Type expr: Variable: 5
          └──Type expr: Variable: 2
       └──Desc: Function
          └──Pattern:
             └──Type expr: Constructor: list
                └──Type expr: Variable: 5
             └──Desc: Construct
                └──Constructor description:
                   └──Name: Cons
                   └──Constructor argument type:
                      └──Type expr: Tuple
                         └──Type expr: Variable: 5
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 5
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 5
                └──Pattern:
                   └──Type expr: Tuple
                      └──Type expr: Variable: 5
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 5
                   └──Desc: Tuple
                      └──Pattern:
                         └──Type expr: Variable: 5
                         └──Desc: Variable: x
                      └──Pattern:
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 5
                         └──Desc: Any
          └──Expression:
             └──Type expr: Variable: 2
             └──Desc: Variable
                └──Variable: x
                └──Type expr: Variable: 2 |}]


let%expect_test "annotation - identity" =
  let exp =
    (* exists 'a -> fun (x : 'a) -> x *)
    Pexp_exists
      ( [ "a" ]
      , Pexp_fun (Ppat_constraint (Ppat_var "x", Ptyp_var "a"), Pexp_var "x") )
  in
  print_infer_result ~env:Env.empty exp;
  [%expect
    {|
    Variables: 3,3,3
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Variable: 3
          └──Type expr: Variable: 3
       └──Desc: Function
          └──Pattern:
             └──Type expr: Variable: 3
             └──Desc: Variable: x
          └──Expression:
             └──Type expr: Variable: 3
             └──Desc: Variable
                └──Variable: x |}]


let%expect_test "annotation - identity" =
  let exp =
    (* forall 'a -> fun (x : 'a) -> x *)
    Pexp_forall
      ( [ "a" ]
      , Pexp_fun (Ppat_constraint (Ppat_var "x", Ptyp_var "a"), Pexp_var "x") )
  in
  print_infer_result ~env:Env.empty exp;
  [%expect
    {|
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Variable: 11
          └──Type expr: Variable: 11
       └──Desc: Function
          └──Pattern:
             └──Type expr: Variable: 6
             └──Desc: Variable: x
          └──Expression:
             └──Type expr: Variable: 6
             └──Desc: Variable
                └──Variable: x |}]


let%expect_test "annotation - succ" =
  let exp =
    (* exists 'a -> fun (x : 'a) -> x + 1 *)
    Pexp_exists
      ( [ "a" ]
      , Pexp_fun
          ( Ppat_constraint (Ppat_var "x", Ptyp_var "a")
          , Pexp_app
              ( Pexp_app (Pexp_prim Prim_add, Pexp_var "x")
              , Pexp_const (Const_int 1) ) ) )
  in
  print_infer_result ~env:Env.empty exp;
  [%expect
    {|
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Constructor: int
          └──Type expr: Constructor: int
       └──Desc: Function
          └──Pattern:
             └──Type expr: Constructor: int
             └──Desc: Variable: x
          └──Expression:
             └──Type expr: Constructor: int
             └──Desc: Application
                └──Expression:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: int
                      └──Type expr: Constructor: int
                   └──Desc: Application
                      └──Expression:
                         └──Type expr: Arrow
                            └──Type expr: Constructor: int
                            └──Type expr: Arrow
                               └──Type expr: Constructor: int
                               └──Type expr: Constructor: int
                         └──Desc: Primitive: (+)
                      └──Expression:
                         └──Type expr: Constructor: int
                         └──Desc: Variable
                            └──Variable: x
                └──Expression:
                   └──Type expr: Constructor: int
                   └──Desc: Constant: 1 |}]


let%expect_test "annotation - succ" =
  let exp =
    (* forall 'a -> fun (x : 'a) -> x + 1 *)
    Pexp_forall
      ( [ "a" ]
      , Pexp_fun
          ( Ppat_constraint (Ppat_var "x", Ptyp_var "a")
          , Pexp_app
              ( Pexp_app (Pexp_prim Prim_add, Pexp_var "x")
              , Pexp_const (Const_int 1) ) ) )
  in
  print_infer_result ~env:Env.empty exp;
  [%expect
    {|
    ("Cannot unify types"
     ("Type_expr.decode type_expr1" (Type 11 (Former (Constr () int))))
     ("Type_expr.decode type_expr2" (Type 24 (Var 24)))) |}]


let%expect_test "let - identity" =
  let exp =
    (* let id x = x in id id () *)
    Pexp_let
      ( Nonrecursive
      , [ { pvb_forall_vars = []
          ; pvb_pat = Ppat_var "id"
          ; pvb_expr = Pexp_fun (Ppat_var "x", Pexp_var "x")
          }
        ]
      , Pexp_app (Pexp_app (Pexp_var "id", Pexp_var "id"), Pexp_const Const_unit)
      )
  in
  print_infer_result ~env:Env.empty exp;
  [%expect
    {|
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Constructor: unit
       └──Desc: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 3
                      └──Type expr: Variable: 3
                   └──Desc: Variable: id
                └──Abstraction:
                   └──Variables: 3,3
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 3
                         └──Type expr: Variable: 3
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 3
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: 3
                            └──Desc: Variable
                               └──Variable: x
          └──Expression:
             └──Type expr: Constructor: unit
             └──Desc: Application
                └──Expression:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: unit
                      └──Type expr: Constructor: unit
                   └──Desc: Application
                      └──Expression:
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Constructor: unit
                               └──Type expr: Constructor: unit
                            └──Type expr: Arrow
                               └──Type expr: Constructor: unit
                               └──Type expr: Constructor: unit
                         └──Desc: Variable
                            └──Variable: id
                            └──Type expr: Arrow
                               └──Type expr: Constructor: unit
                               └──Type expr: Constructor: unit
                      └──Expression:
                         └──Type expr: Arrow
                            └──Type expr: Constructor: unit
                            └──Type expr: Constructor: unit
                         └──Desc: Variable
                            └──Variable: id
                            └──Type expr: Constructor: unit
                └──Expression:
                   └──Type expr: Constructor: unit
                   └──Desc: Constant: () |}]


(* ('a -> 'a) -> (unit -> 'b) *)
(* 'a -> 'a *)

let%expect_test "let - map" =
  let env = add_list Env.empty in
  let exp =
    (* let rec map f xs = match xs with (Nil -> Nil | Cons (x, xs) -> Cons (f x, map f xs)) in let f x = x + 1 in map f Nil *)
    Pexp_let
      ( Recursive
      , [ { pvb_forall_vars = []
          ; pvb_pat = Ppat_var "map"
          ; pvb_expr =
              Pexp_fun
                ( Ppat_var "f"
                , Pexp_fun
                    ( Ppat_var "xs"
                    , Pexp_match
                        ( Pexp_var "xs"
                        , [ { pc_lhs = Ppat_construct ("Nil", None)
                            ; pc_rhs = Pexp_construct ("Nil", None)
                            }
                          ; { pc_lhs =
                                Ppat_construct
                                  ( "Cons"
                                  , Some
                                      ( []
                                      , Ppat_tuple
                                          [ Ppat_var "x"; Ppat_var "xs" ] ) )
                            ; pc_rhs =
                                Pexp_construct
                                  ( "Cons"
                                  , Some
                                      (Pexp_tuple
                                         [ Pexp_app (Pexp_var "f", Pexp_var "x")
                                         ; Pexp_app
                                             ( Pexp_app
                                                 (Pexp_var "map", Pexp_var "f")
                                             , Pexp_var "xs" )
                                         ]) )
                            }
                          ] ) ) )
          }
        ]
      , Pexp_let
          ( Nonrecursive
          , [ { pvb_forall_vars = []
              ; pvb_pat = Ppat_var "f"
              ; pvb_expr =
                  Pexp_fun
                    ( Ppat_var "x"
                    , Pexp_app
                        ( Pexp_app (Pexp_prim Prim_add, Pexp_var "x")
                        , Pexp_const (Const_int 1) ) )
              }
            ]
          , Pexp_app
              ( Pexp_app (Pexp_var "map", Pexp_var "f")
              , Pexp_construct ("Nil", None) ) ) )
  in
  print_infer_result ~env exp;
  [%expect
    {|
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Constructor: list
          └──Type expr: Constructor: int
       └──Desc: Let rec
          └──Value bindings:
             └──Value binding:
                └──Variable: map
                └──Abstraction:
                   └──Variables: 28,39
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: 39
                            └──Type expr: Variable: 28
                         └──Type expr: Arrow
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: 39
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: 28
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Variable: 39
                               └──Type expr: Variable: 28
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: 39
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: 28
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: 39
                                  └──Desc: Variable: xs
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: 28
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Variable: 39
                                        └──Desc: Variable
                                           └──Variable: xs
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: 39
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: 39
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: 39
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: 28
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: 28
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: 39
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 39
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: 39
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: 39
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 39
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: 39
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Variable: 39
                                                          └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: 39
                                                          └──Desc: Variable: xs
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: 28
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 28
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: 28
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: 28
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 28
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: 28
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Variable: 28
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: 39
                                                                   └──Type expr: Variable: 28
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Variable: 39
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: 28
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: 39
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: 28
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Variable: 39
                                                                            └──Type expr: Variable: 28
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Variable: 39
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Variable: 28
                                                                      └──Desc: Variable
                                                                         └──Variable: map
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: 39
                                                                         └──Type expr: Variable: 28
                                                                      └──Desc: Variable
                                                                         └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: 39
                                                                └──Desc: Variable
                                                                   └──Variable: xs
          └──Expression:
             └──Type expr: Constructor: list
                └──Type expr: Constructor: int
             └──Desc: Let
                └──Value bindings:
                   └──Value binding:
                      └──Pattern:
                         └──Type expr: Arrow
                            └──Type expr: Constructor: int
                            └──Type expr: Constructor: int
                         └──Desc: Variable: f
                      └──Abstraction:
                         └──Variables:
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: int
                               └──Type expr: Constructor: int
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: int
                                           └──Type expr: Constructor: int
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: int
                                              └──Desc: Primitive: (+)
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 1
                └──Expression:
                   └──Type expr: Constructor: list
                      └──Type expr: Constructor: int
                   └──Desc: Application
                      └──Expression:
                         └──Type expr: Arrow
                            └──Type expr: Constructor: list
                               └──Type expr: Constructor: int
                            └──Type expr: Constructor: list
                               └──Type expr: Constructor: int
                         └──Desc: Application
                            └──Expression:
                               └──Type expr: Arrow
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: int
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: list
                                        └──Type expr: Constructor: int
                                     └──Type expr: Constructor: list
                                        └──Type expr: Constructor: int
                               └──Desc: Variable
                                  └──Variable: map
                                  └──Type expr: Constructor: int
                                  └──Type expr: Constructor: int
                            └──Expression:
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: int
                                  └──Type expr: Constructor: int
                               └──Desc: Variable
                                  └──Variable: f
                      └──Expression:
                         └──Type expr: Constructor: list
                            └──Type expr: Constructor: int
                         └──Desc: Construct
                            └──Constructor description:
                               └──Name: Nil
                               └──Constructor type:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Constructor: int |}]


let%expect_test "let rec - monomorphic recursion" =
  let env = add_list Env.empty in
  let exp =
    (* let rec id x = x and id_int x = id (x : int) in id_int *)
    Pexp_let
      ( Recursive
      , [ { pvb_forall_vars = []
          ; pvb_pat = Ppat_var "id"
          ; pvb_expr = Pexp_fun (Ppat_var "x", Pexp_var "x")
          }
        ; { pvb_forall_vars = []
          ; pvb_pat = Ppat_var "id_int"
          ; pvb_expr =
              Pexp_fun
                ( Ppat_var "x"
                , Pexp_app
                    ( Pexp_var "id"
                    , Pexp_constraint (Pexp_var "x", Ptyp_constr ([], "int")) )
                )
          }
        ]
      , Pexp_var "id" )
  in
  print_infer_result ~env exp;
  [%expect
    {|
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Constructor: int
          └──Type expr: Constructor: int
       └──Desc: Let rec
          └──Value bindings:
             └──Value binding:
                └──Variable: id_int
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Variable
                               └──Variable: x
             └──Value binding:
                └──Variable: id
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: int
                                  └──Desc: Variable
                                     └──Variable: id
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable
                                     └──Variable: x
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Constructor: int
                └──Type expr: Constructor: int
             └──Desc: Variable
                └──Variable: id |}]


let%expect_test "let rec - mutual recursion (monomorphic)" =
  let exp =
    (* let rec is_even x = if x = 0 then true else is_odd (x - 1) and is_odd x = if x = 1 then true else is_even (x - 1) in is_even *)
    Pexp_let
      ( Recursive
      , [ { pvb_forall_vars = []
          ; pvb_pat = Ppat_var "is_even"
          ; pvb_expr =
              Pexp_fun
                ( Ppat_var "x"
                , Pexp_ifthenelse
                    ( Pexp_app
                        ( Pexp_app (Pexp_prim Prim_eq, Pexp_var "x")
                        , Pexp_const (Const_int 0) )
                    , Pexp_const (Const_bool true)
                    , Pexp_app
                        ( Pexp_var "is_odd"
                        , Pexp_app
                            ( Pexp_app (Pexp_prim Prim_sub, Pexp_var "x")
                            , Pexp_const (Const_int 1) ) ) ) )
          }
        ; { pvb_forall_vars = []
          ; pvb_pat = Ppat_var "is_odd"
          ; pvb_expr =
              Pexp_fun
                ( Ppat_var "x"
                , Pexp_ifthenelse
                    ( Pexp_app
                        ( Pexp_app (Pexp_prim Prim_eq, Pexp_var "x")
                        , Pexp_const (Const_int 1) )
                    , Pexp_const (Const_bool true)
                    , Pexp_app
                        ( Pexp_var "is_even"
                        , Pexp_app
                            ( Pexp_app (Pexp_prim Prim_sub, Pexp_var "x")
                            , Pexp_const (Const_int 1) ) ) ) )
          }
        ]
      , Pexp_var "is_even" )
  in
  print_infer_result ~env:Env.empty exp;
  [%expect
    {|
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Constructor: int
          └──Type expr: Constructor: bool
       └──Desc: Let rec
          └──Value bindings:
             └──Value binding:
                └──Variable: is_odd
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: bool
                            └──Desc: If
                               └──Expression:
                                  └──Type expr: Constructor: bool
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: int
                                           └──Type expr: Constructor: bool
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: bool
                                              └──Desc: Primitive: (=)
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 0
                               └──Expression:
                                  └──Type expr: Constructor: bool
                                  └──Desc: Constant: true
                               └──Expression:
                                  └──Type expr: Constructor: bool
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: int
                                           └──Type expr: Constructor: bool
                                        └──Desc: Variable
                                           └──Variable: is_odd
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: int
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: int
                                                          └──Type expr: Constructor: int
                                                    └──Desc: Primitive: (-)
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Constant: 1
             └──Value binding:
                └──Variable: is_even
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: bool
                            └──Desc: If
                               └──Expression:
                                  └──Type expr: Constructor: bool
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: int
                                           └──Type expr: Constructor: bool
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: bool
                                              └──Desc: Primitive: (=)
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 1
                               └──Expression:
                                  └──Type expr: Constructor: bool
                                  └──Desc: Constant: true
                               └──Expression:
                                  └──Type expr: Constructor: bool
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: int
                                           └──Type expr: Constructor: bool
                                        └──Desc: Variable
                                           └──Variable: is_even
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: int
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: int
                                                          └──Type expr: Constructor: int
                                                    └──Desc: Primitive: (-)
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Constant: 1
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Constructor: int
                └──Type expr: Constructor: bool
             └──Desc: Variable
                └──Variable: is_even |}]


let%expect_test "let rec - mutual recursion (polymorphic)" =
  let exp =
    (* let rec foo x = 1 and bar y = true in foo *)
    Pexp_let
      ( Recursive
      , [ { pvb_forall_vars = []
          ; pvb_pat = Ppat_var "foo"
          ; pvb_expr = Pexp_fun (Ppat_var "x", Pexp_const (Const_int 1))
          }
        ; { pvb_forall_vars = []
          ; pvb_pat = Ppat_var "bar"
          ; pvb_expr = Pexp_fun (Ppat_var "y", Pexp_const (Const_bool true))
          }
        ]
      , Pexp_var "foo" )
  in
  print_infer_result ~env:Env.empty exp;
  [%expect
    {|
    Variables: 16
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Variable: 16
          └──Type expr: Constructor: int
       └──Desc: Let rec
          └──Value bindings:
             └──Value binding:
                └──Variable: bar
                └──Abstraction:
                   └──Variables: 9
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 3
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 3
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Constant: 1
             └──Value binding:
                └──Variable: foo
                └──Abstraction:
                   └──Variables: 3
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 9
                         └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 9
                            └──Desc: Variable: y
                         └──Expression:
                            └──Type expr: Constructor: bool
                            └──Desc: Constant: true
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Variable: 16
                └──Type expr: Constructor: int
             └──Desc: Variable
                └──Variable: foo
                └──Type expr: Variable: 16 |}]


let%expect_test "f-pottier elaboration 1" =
  let exp =
    (* let u = (fun f -> ()) (fun x -> x) in u *)
    Pexp_let
      ( Nonrecursive
      , [ { pvb_forall_vars = []
          ; pvb_pat = Ppat_var "u"
          ; pvb_expr =
              Pexp_app
                ( Pexp_fun (Ppat_var "f", Pexp_const Const_unit)
                , Pexp_fun (Ppat_var "x", Pexp_var "x") )
          }
        ]
      , Pexp_var "u" )
  in
  print_infer_result ~env:Env.empty exp;
  [%expect
    {|
    Variables: 12,12
    Expression:
    └──Expression:
       └──Type expr: Constructor: unit
       └──Desc: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: unit
                   └──Desc: Variable: u
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: unit
                      └──Desc: Application
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 12
                                  └──Type expr: Variable: 12
                               └──Type expr: Constructor: unit
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 12
                                     └──Type expr: Variable: 12
                                  └──Desc: Variable: f
                               └──Expression:
                                  └──Type expr: Constructor: unit
                                  └──Desc: Constant: ()
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: 12
                               └──Type expr: Variable: 12
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: 12
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Variable: 12
                                  └──Desc: Variable
                                     └──Variable: x
          └──Expression:
             └──Type expr: Constructor: unit
             └──Desc: Variable
                └──Variable: u |}]


let%expect_test "let rec - polymorphic recursion" =
  let env = add_list Env.empty in
  let exp =
    (* let rec (type a) id : a -> a = fun x -> x and id_int x = id (x : int) in id *)
    Pexp_let
      ( Recursive
      , [ { pvb_forall_vars = [ "a" ]
          ; pvb_pat =
              Ppat_constraint
                (Ppat_var "id", Ptyp_arrow (Ptyp_var "a", Ptyp_var "a"))
          ; pvb_expr = Pexp_fun (Ppat_var "x", Pexp_var "x")
          }
        ; { pvb_forall_vars = []
          ; pvb_pat = Ppat_var "id_int"
          ; pvb_expr =
              Pexp_fun
                ( Ppat_var "x"
                , Pexp_app
                    ( Pexp_var "id"
                    , Pexp_constraint (Pexp_var "x", Ptyp_constr ([], "int")) )
                )
          }
        ]
      , Pexp_var "id" )
  in
  print_infer_result ~env exp;
  [%expect
    {|
    Variables: 38
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Variable: 38
          └──Type expr: Variable: 38
       └──Desc: Let rec
          └──Value bindings:
             └──Value binding:
                └──Variable: id
                └──Abstraction:
                   └──Variables: 3
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 27
                         └──Type expr: Variable: 27
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 27
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: 27
                            └──Desc: Variable
                               └──Variable: x
             └──Value binding:
                └──Variable: id_int
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: int
                                  └──Desc: Variable
                                     └──Variable: id
                                     └──Type expr: Constructor: int
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable
                                     └──Variable: x
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Variable: 38
                └──Type expr: Variable: 38
             └──Desc: Variable
                └──Variable: id
                └──Type expr: Variable: 38 |}]


let add_eq env =
  let name = "eq" in
  let a = Type_var.make () in
  let b = Type_var.make () in
  let params = [ a; b ] in
  let a' = Type_expr.make (Ttyp_var a)
  and b' = Type_expr.make (Ttyp_var b) in
  let type_ = Type_expr.make (Ttyp_constr ([ a'; b' ], name)) in
  Env.add_type_decl
    env
    { type_name = name
    ; type_kind =
        Type_variant
          [ { constructor_name = "Refl"
            ; constructor_alphas = params
            ; constructor_arg = None
            ; constructor_type = type_
            ; constructor_constraints = [ a', b' ]
            }
          ]
    }


let%expect_test "ambiv-f" =
  let env = add_eq Env.empty in
  let exp =
    Pexp_let
      ( Nonrecursive
      , [ { pvb_forall_vars = [ "a" ]
          ; pvb_pat = Ppat_var "f"
          ; pvb_expr =
              Pexp_fun
                ( Ppat_constraint
                    ( Ppat_var "x"
                    , Ptyp_constr
                        ([ Ptyp_var "a"; Ptyp_constr ([], "int") ], "eq") )
                , Pexp_match
                    ( Pexp_var "x"
                    , [ { pc_lhs = Ppat_construct ("Refl", None)
                        ; pc_rhs = Pexp_const (Const_int 1)
                        }
                      ] ) )
          }
        ]
      , Pexp_const Const_unit )
  in
  (* print_constraint_result ~env exp; *)
  print_infer_result ~env exp;
  [%expect
    {|
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Constructor: unit
       └──Desc: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: 13
                         └──Type expr: Constructor: int
                      └──Type expr: Constructor: int
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: 13
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: 13
                            └──Type expr: Constructor: int
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: 13
                               └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: 13
                                     └──Type expr: Constructor: int
                                  └──Desc: Variable
                                     └──Variable: x
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: 13
                                  └──Type expr: Constructor: int
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: 13
                                           └──Type expr: Constructor: int
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Refl
                                              └──Constructor type:
                                                 └──Type expr: Constructor: eq
                                                    └──Type expr: Variable: 13
                                                    └──Type expr: Constructor: int
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 1
          └──Expression:
             └──Type expr: Constructor: unit
             └──Desc: Constant: () |}]


let%expect_test "ambiv-f1" =
  let env = add_eq Env.empty in
  let exp =
    Pexp_let
      ( Nonrecursive
      , [ { pvb_forall_vars = [ "a" ]
          ; pvb_pat = Ppat_var "f1"
          ; pvb_expr =
              Pexp_fun
                ( Ppat_constraint
                    ( Ppat_var "x"
                    , Ptyp_constr
                        ([ Ptyp_var "a"; Ptyp_constr ([], "int") ], "eq") )
                , Pexp_match
                    ( Pexp_var "x"
                    , [ { pc_lhs = Ppat_construct ("Refl", None)
                        ; pc_rhs = Pexp_const (Const_bool true)
                        }
                      ] ) )
          }
        ]
      , Pexp_const Const_unit )
  in
  (* print_constraint_result ~env exp; *)
  print_infer_result ~env exp;
  [%expect
    {|
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Constructor: unit
       └──Desc: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: 13
                         └──Type expr: Constructor: int
                      └──Type expr: Constructor: bool
                   └──Desc: Variable: f1
                └──Abstraction:
                   └──Variables: 13
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: 13
                            └──Type expr: Constructor: int
                         └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: 13
                               └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: bool
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: 13
                                     └──Type expr: Constructor: int
                                  └──Desc: Variable
                                     └──Variable: x
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: 13
                                  └──Type expr: Constructor: int
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: 13
                                           └──Type expr: Constructor: int
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Refl
                                              └──Constructor type:
                                                 └──Type expr: Constructor: eq
                                                    └──Type expr: Variable: 13
                                                    └──Type expr: Constructor: int
                                     └──Expression:
                                        └──Type expr: Constructor: bool
                                        └──Desc: Constant: true
          └──Expression:
             └──Type expr: Constructor: unit
             └──Desc: Constant: () |}]


let%expect_test "ambiv-f2" =
  let env = add_eq Env.empty in
  let exp =
    Pexp_let
      ( Nonrecursive
      , [ { pvb_forall_vars = [ "a" ]
          ; pvb_pat = Ppat_var "f2"
          ; pvb_expr =
              Pexp_fun
                ( Ppat_constraint
                    ( Ppat_var "x"
                    , Ptyp_constr
                        ([ Ptyp_var "a"; Ptyp_constr ([], "int") ], "eq") )
                , Pexp_fun
                    ( Ppat_constraint (Ppat_var "y", Ptyp_var "a")
                    , Pexp_match
                        ( Pexp_var "x"
                        , [ { pc_lhs = Ppat_construct ("Refl", None)
                            ; pc_rhs =
                                Pexp_app
                                  ( Pexp_app (Pexp_prim Prim_eq, Pexp_var "y")
                                  , Pexp_const (Const_int 0) )
                            }
                          ] ) ) )
          }
        ]
      , Pexp_const Const_unit )
  in
  (* print_constraint_result ~env exp; *)
  print_infer_result ~env exp;
  [%expect
    {|
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Constructor: unit
       └──Desc: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: 13
                         └──Type expr: Constructor: int
                      └──Type expr: Arrow
                         └──Type expr: Variable: 13
                         └──Type expr: Constructor: bool
                   └──Desc: Variable: f2
                └──Abstraction:
                   └──Variables: 13
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: 13
                            └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Variable: 13
                            └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: 13
                               └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: 13
                               └──Type expr: Constructor: bool
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: 13
                                  └──Desc: Variable: y
                               └──Expression:
                                  └──Type expr: Constructor: bool
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: 13
                                           └──Type expr: Constructor: int
                                        └──Desc: Variable
                                           └──Variable: x
                                     └──Type expr: Constructor: eq
                                        └──Type expr: Variable: 13
                                        └──Type expr: Constructor: int
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: 13
                                                 └──Type expr: Constructor: int
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Refl
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: 13
                                                          └──Type expr: Constructor: int
                                           └──Expression:
                                              └──Type expr: Constructor: bool
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: int
                                                       └──Type expr: Constructor: bool
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: 13
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: int
                                                                └──Type expr: Constructor: bool
                                                          └──Desc: Primitive: (=)
                                                       └──Expression:
                                                          └──Type expr: Variable: 13
                                                          └──Desc: Variable
                                                             └──Variable: y
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Constant: 0
          └──Expression:
             └──Type expr: Constructor: unit
             └──Desc: Constant: () |}]


let%expect_test "ambiv-g" =
  let env = add_eq Env.empty in
  let exp =
    Pexp_let
      ( Nonrecursive
      , [ { pvb_forall_vars = [ "a" ]
          ; pvb_pat = Ppat_var "g"
          ; pvb_expr =
              Pexp_fun
                ( Ppat_constraint
                    ( Ppat_var "x"
                    , Ptyp_constr
                        ([ Ptyp_var "a"; Ptyp_constr ([], "int") ], "eq") )
                , Pexp_fun
                    ( Ppat_constraint (Ppat_var "y", Ptyp_var "a")
                    , Pexp_constraint
                        ( Pexp_match
                            ( Pexp_var "x"
                            , [ { pc_lhs = Ppat_construct ("Refl", None)
                                ; pc_rhs =
                                    Pexp_ifthenelse
                                      ( Pexp_app
                                          ( Pexp_app
                                              (Pexp_prim Prim_eq, Pexp_var "y")
                                          , Pexp_const (Const_int 0) )
                                      , Pexp_var "y"
                                      , Pexp_const (Const_int 0) )
                                }
                              ] )
                        , Ptyp_var "a" ) ) )
          }
        ]
      , Pexp_const Const_unit )
  in
  (* print_constraint_result ~env exp; *)
  print_infer_result ~env exp;
  [%expect
    {|
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Constructor: unit
       └──Desc: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: 13
                         └──Type expr: Constructor: int
                      └──Type expr: Arrow
                         └──Type expr: Variable: 13
                         └──Type expr: Variable: 13
                   └──Desc: Variable: g
                └──Abstraction:
                   └──Variables: 13
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: 13
                            └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Variable: 13
                            └──Type expr: Variable: 13
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: 13
                               └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: 13
                               └──Type expr: Variable: 13
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: 13
                                  └──Desc: Variable: y
                               └──Expression:
                                  └──Type expr: Variable: 13
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: 13
                                           └──Type expr: Constructor: int
                                        └──Desc: Variable
                                           └──Variable: x
                                     └──Type expr: Constructor: eq
                                        └──Type expr: Variable: 13
                                        └──Type expr: Constructor: int
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: 13
                                                 └──Type expr: Constructor: int
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Refl
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: 13
                                                          └──Type expr: Constructor: int
                                           └──Expression:
                                              └──Type expr: Variable: 13
                                              └──Desc: If
                                                 └──Expression:
                                                    └──Type expr: Constructor: bool
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: bool
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: 13
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: int
                                                                      └──Type expr: Constructor: bool
                                                                └──Desc: Primitive: (=)
                                                             └──Expression:
                                                                └──Type expr: Variable: 13
                                                                └──Desc: Variable
                                                                   └──Variable: y
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Constant: 0
                                                 └──Expression:
                                                    └──Type expr: Variable: 13
                                                    └──Desc: Variable
                                                       └──Variable: y
                                                 └──Expression:
                                                    └──Type expr: Variable: 13
                                                    └──Desc: Constant: 0
          └──Expression:
             └──Type expr: Constructor: unit
             └──Desc: Constant: () |}]


let%expect_test "ambiv-p" =
  let env = add_eq Env.empty in
  let exp =
    Pexp_let
      ( Nonrecursive
      , [ { pvb_forall_vars = [ "a" ]
          ; pvb_pat = Ppat_var "f"
          ; pvb_expr =
              Pexp_fun
                ( Ppat_constraint
                    ( Ppat_var "x"
                    , Ptyp_constr
                        ([ Ptyp_var "a"; Ptyp_constr ([], "int") ], "eq") )
                , Pexp_let
                    ( Nonrecursive
                    , [ { pvb_forall_vars = []
                        ; pvb_pat = Ppat_var "y"
                        ; pvb_expr =
                            Pexp_match
                              ( Pexp_var "x"
                              , [ { pc_lhs = Ppat_construct ("Refl", None)
                                  ; pc_rhs = Pexp_const (Const_int 1)
                                  }
                                ] )
                        }
                      ]
                    , Pexp_app
                        ( Pexp_app (Pexp_prim Prim_mul, Pexp_var "y")
                        , Pexp_const (Const_int 2) ) ) )
          }
        ]
      , Pexp_const Const_unit )
  in
  (* print_constraint_result ~env exp; *)
  print_infer_result ~env exp;
  [%expect
    {|
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Constructor: unit
       └──Desc: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: 13
                         └──Type expr: Constructor: int
                      └──Type expr: Constructor: int
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: 13
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: 13
                            └──Type expr: Constructor: int
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: 13
                               └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Let
                               └──Value bindings:
                                  └──Value binding:
                                     └──Pattern:
                                        └──Type expr: Constructor: int
                                        └──Desc: Variable: y
                                     └──Abstraction:
                                        └──Variables:
                                        └──Expression:
                                           └──Type expr: Constructor: int
                                           └──Desc: Match
                                              └──Expression:
                                                 └──Type expr: Constructor: eq
                                                    └──Type expr: Variable: 13
                                                    └──Type expr: Constructor: int
                                                 └──Desc: Variable
                                                    └──Variable: x
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: 13
                                                 └──Type expr: Constructor: int
                                              └──Cases:
                                                 └──Case:
                                                    └──Pattern:
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: 13
                                                          └──Type expr: Constructor: int
                                                       └──Desc: Construct
                                                          └──Constructor description:
                                                             └──Name: Refl
                                                             └──Constructor type:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: 13
                                                                   └──Type expr: Constructor: int
                                                    └──Expression:
                                                       └──Type expr: Constructor: int
                                                       └──Desc: Constant: 1
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: int
                                           └──Type expr: Constructor: int
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: int
                                              └──Desc: Primitive: (*)
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: y
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 2
          └──Expression:
             └──Type expr: Constructor: unit
             └──Desc: Constant: () |}]


let%expect_test "coerce" =
  (* let (type a b) coerce eq (x : a) = match (eq : (a, b) eq) with Refl -> (x : b) in () *)
  let env = add_eq Env.empty in
  let exp =
    Pexp_let
      ( Nonrecursive
      , [ { pvb_forall_vars = [ "a"; "b" ]
          ; pvb_pat = Ppat_var "coerce"
          ; pvb_expr =
              Pexp_fun
                ( Ppat_constraint
                    ( Ppat_var "eq"
                    , Ptyp_constr ([ Ptyp_var "a"; Ptyp_var "b" ], "eq") )
                , Pexp_fun
                    ( Ppat_constraint
                        (Ppat_var "x", Ptyp_constr ([ Ptyp_var "a" ], "t"))
                    , Pexp_constraint
                        ( Pexp_match
                            ( Pexp_var "eq"
                            , [ { pc_lhs = Ppat_construct ("Refl", None)
                                ; pc_rhs = Pexp_var "x"
                                }
                              ] )
                        , Ptyp_constr ([ Ptyp_var "b" ], "t") ) ) )
          }
        ]
      , Pexp_const Const_unit )
  in
  (* print_constraint_result ~env exp; *)
  print_infer_result ~env exp;
  [%expect
    {|
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Constructor: unit
       └──Desc: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: 11
                         └──Type expr: Variable: 12
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: 11
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: 12
                   └──Desc: Variable: coerce
                └──Abstraction:
                   └──Variables: 11,12
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: 11
                            └──Type expr: Variable: 12
                         └──Type expr: Arrow
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: 11
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: 12
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: 11
                               └──Type expr: Variable: 12
                            └──Desc: Variable: eq
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: 11
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: 12
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: 11
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: 12
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: 11
                                           └──Type expr: Variable: 12
                                        └──Desc: Variable
                                           └──Variable: eq
                                     └──Type expr: Constructor: eq
                                        └──Type expr: Variable: 11
                                        └──Type expr: Variable: 12
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: 11
                                                 └──Type expr: Variable: 12
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Refl
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: 11
                                                          └──Type expr: Variable: 12
                                           └──Expression:
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Variable: 12
                                              └──Desc: Variable
                                                 └──Variable: x
          └──Expression:
             └──Type expr: Constructor: unit
             └──Desc: Constant: () |}]


(* let%expect_test "solve" =
   let open Constraint in
   let cst =
   let a1 = fresh () in
   let a2 = fresh () in
   forall
   [ a1; a2 ]
   (def_poly
   ~flexible_vars:[]
   ~bindings:[ "x" #= a1 ]
   ~in_:[ Var a1, Var a2 ] #=> (inst "x" a2))
   in
   print_solve_result cst;
   [%expect
    {|
    ((Forall (481 482))
     ((Def_poly ()) ((x 481))
      ((Implication (((Var 481) (Var 482)))) ((Instance x) 482))))
    Constraint is true. |}] *)
(*
   let%expect_test "solve-1" =
   let open Constraint in
   let open Algebra.Type_former in
   let cst =
   let a1 = fresh () in
   let a2 = fresh () in
   let a3 = fresh () in
   forall
   [ a1 ]
   (def_poly
   ~flexible_vars:
   [ a2, Some (Former (Constr ([], "int")))
           ; a3, Some (Former (Constr ([ a1; a2 ], "eq")))
           ]
   ~bindings:[ "x" #= a3 ]
   ~in_:
   (let a4 = fresh () in
   let a5 = fresh () in
   let a6 = fresh () in
   let a7 = fresh () in
   exists
   [ a4, None ]
   (inst "x" a4
   &~ exists
   [ a5, None
                   ; a6, Some (Former (Constr ([], "int")))
                   ; a7, Some (Former (Constr ([ a5; a6 ], "eq")))
                   ]
   (a4 =~ a7 &~ [ Var a5, Var a6 ] #=> (return ())))))
   in
   print_solve_result cst;
   [%expect
    {|
    ((Forall (483))
     ((Def_poly
       ((484 ((Former (Constr () int)))) (485 ((Former (Constr (483 484) eq))))))
      ((x 485))
      ((Exist ((486 ())))
       ((Conj ((Instance x) 486))
        ((Exist
          ((487 ()) (488 ((Former (Constr () int))))
           (489 ((Former (Constr (487 488) eq))))))
         ((Conj ((Eq 486) 489)) ((Implication (((Var 487) (Var 488)))) Return)))))))
    Constraint is true. |}] *)

let%expect_test "abbrev - morel" =
  let abbrevs =
    let open Typing.Private.Algebra.Type_former in
    let abbrev_k =
      let a = Abbrev_type.make_var () in
      let pair = Abbrev_type.make_former (Tuple [ a; a ]) in
      Constr ([ a ], "K"), pair
    in
    let abbrev_f =
      let a = Abbrev_type.make_var () in
      let arr = Abbrev_type.make_former (Arrow (a, a)) in
      Constr ([ a ], "F"), arr
    in
    let abbrev_g =
      let a = Abbrev_type.(make_var ()) in
      let k = Abbrev_type.(make_former (Constr ([ a ], "K"))) in
      let f = Abbrev_type.(make_former (Constr ([ k ], "F"))) in
      Constr ([ a ], "G"), f
    in
    Abbreviations.empty
    |> Abbreviations.add ~abbrev:abbrev_k
    |> Abbreviations.add ~abbrev:abbrev_f
    |> Abbreviations.add ~abbrev:abbrev_g
  in
  let exp =
    Pexp_let
      ( Nonrecursive
      , [ { pvb_forall_vars = []
          ; pvb_pat = Ppat_var "f"
          ; pvb_expr =
              Pexp_constraint
                ( Pexp_fun (Ppat_var "x", Pexp_var "x")
                , Ptyp_constr ([ Ptyp_constr ([], "int") ], "G") )
          }
        ]
      , Pexp_exists
          ( [ "a" ]
          , Pexp_fun
              ( Ppat_constraint
                  (Ppat_var "x", Ptyp_constr ([ Ptyp_var "a" ], "K"))
              , Pexp_app (Pexp_var "f", Pexp_var "x") ) ) )
  in
  print_infer_result ~abbrevs ~env:Env.empty exp;
  [%expect
    {|
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Constructor: K
             └──Type expr: Constructor: int
          └──Type expr: Constructor: K
             └──Type expr: Constructor: int
       └──Desc: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: G
                      └──Type expr: Constructor: int
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: G
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: K
                               └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: K
                               └──Type expr: Constructor: int
                            └──Desc: Variable
                               └──Variable: x
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Constructor: K
                   └──Type expr: Constructor: int
                └──Type expr: Constructor: K
                   └──Type expr: Constructor: int
             └──Desc: Function
                └──Pattern:
                   └──Type expr: Constructor: K
                      └──Type expr: Constructor: int
                   └──Desc: Variable: x
                └──Expression:
                   └──Type expr: Constructor: K
                      └──Type expr: Constructor: int
                   └──Desc: Application
                      └──Expression:
                         └──Type expr: Arrow
                            └──Type expr: Constructor: K
                               └──Type expr: Constructor: int
                            └──Type expr: Constructor: K
                               └──Type expr: Constructor: int
                         └──Desc: Variable
                            └──Variable: f
                      └──Expression:
                         └──Type expr: Constructor: K
                            └──Type expr: Constructor: int
                         └──Desc: Variable
                            └──Variable: x |}]


let add_term env =
  let name = "term" in
  let a = Type_var.make () in
  let a' = Type_expr.make (Ttyp_var a) in
  let alphas = [ a ] in
  let type_ = Type_expr.make (Ttyp_constr ([ a' ], name)) in
  let int = Type_expr.make (Ttyp_constr ([], "int")) in
  let bool = Type_expr.make (Ttyp_constr ([], "bool")) in
  let b1 = Type_var.make () in
  let b2 = Type_var.make () in
  let b1' = Type_expr.make (Ttyp_var b1) in
  let b2' = Type_expr.make (Ttyp_var b2) in
  Env.add_type_decl
    env
    { type_name = name
    ; type_kind =
        Type_variant
          [ { constructor_name = "Int"
            ; constructor_alphas = alphas
            ; constructor_arg =
                Some { constructor_arg_betas = []; constructor_arg_type = int }
            ; constructor_type = type_
            ; constructor_constraints = [ a', int ]
            }
          ; { constructor_name = "Succ"
            ; constructor_alphas = alphas
            ; constructor_arg =
                Some
                  { constructor_arg_betas = []
                  ; constructor_arg_type =
                      Type_expr.make (Ttyp_constr ([ int ], name))
                  }
            ; constructor_type = type_
            ; constructor_constraints = [ a', int ]
            }
          ; { constructor_name = "Bool"
            ; constructor_alphas = alphas
            ; constructor_arg =
                Some { constructor_arg_betas = []; constructor_arg_type = bool }
            ; constructor_type = type_
            ; constructor_constraints = [ a', bool ]
            }
          ; { constructor_name = "If"
            ; constructor_alphas = alphas
            ; constructor_arg =
                Some
                  { constructor_arg_betas = []
                  ; constructor_arg_type =
                      Type_expr.make
                        (Ttyp_tuple
                           [ Type_expr.make (Ttyp_constr ([ bool ], name))
                           ; Type_expr.make (Ttyp_constr ([ a' ], name))
                           ; Type_expr.make (Ttyp_constr ([ a' ], name))
                           ])
                  }
            ; constructor_type = type_
            ; constructor_constraints = []
            }
          ; { constructor_name = "Pair"
            ; constructor_alphas = alphas
            ; constructor_arg =
                Some
                  { constructor_arg_betas = [ b1; b2 ]
                  ; constructor_arg_type =
                      Type_expr.make
                        (Ttyp_tuple
                           [ Type_expr.make (Ttyp_constr ([ b1' ], name))
                           ; Type_expr.make (Ttyp_constr ([ b2' ], name))
                           ])
                  }
            ; constructor_type = type_
            ; constructor_constraints =
                [ a', Type_expr.make (Ttyp_tuple [ b1'; b2' ]) ]
            }
          ; { constructor_name = "Fst"
            ; constructor_alphas = alphas
            ; constructor_arg =
                Some
                  { constructor_arg_betas = [ b1; b2 ]
                  ; constructor_arg_type =
                      Type_expr.make
                        (Ttyp_constr
                           ([ Type_expr.make (Ttyp_tuple [ b1'; b2' ]) ], name))
                  }
            ; constructor_type = type_
            ; constructor_constraints = [ a', b1' ]
            }
          ; { constructor_name = "Snd"
            ; constructor_alphas = alphas
            ; constructor_arg =
                Some
                  { constructor_arg_betas = [ b1; b2 ]
                  ; constructor_arg_type =
                      Type_expr.make
                        (Ttyp_constr
                           ([ Type_expr.make (Ttyp_tuple [ b1'; b2' ]) ], name))
                  }
            ; constructor_type = type_
            ; constructor_constraints = [ a', b2' ]
            }
          ]
    }


let def_fst ~in_ =
  Pexp_let
    ( Nonrecursive
    , [ { pvb_forall_vars = []
        ; pvb_pat = Ppat_var "fst"
        ; pvb_expr =
            Pexp_fun (Ppat_tuple [ Ppat_var "x"; Ppat_any ], Pexp_var "x")
        }
      ]
    , in_ )


let def_snd ~in_ =
  Pexp_let
    ( Nonrecursive
    , [ { pvb_forall_vars = []
        ; pvb_pat = Ppat_var "snd"
        ; pvb_expr =
            Pexp_fun (Ppat_tuple [ Ppat_any; Ppat_var "x" ], Pexp_var "x")
        }
      ]
    , in_ )


let%expect_test "term - eval" =
  (*  let rec eval (type a) (t : a term) : a =
      match t with
      | Int x -> x
      | Succ t -> eval t + 1
      | Bool x -> x
      | If (t1, t2, t3) -> if (eval t1) then (eval t2) else (eval t3)
      | Pair (t1, t2) -> (eval t1, eval t2)
      | Fst t -> fst (eval t)
      | Snd t -> snd (eval t)
  *)
  let env = add_term Env.empty in
  let exp =
    def_fst
      ~in_:
        (def_snd
           ~in_:
             (Pexp_let
                ( Recursive
                , [ { pvb_forall_vars = [ "a" ]
                    ; pvb_pat = Ppat_var "eval"
                    ; pvb_expr =
                        Pexp_fun
                          ( Ppat_constraint
                              ( Ppat_var "t"
                              , Ptyp_constr ([ Ptyp_var "a" ], "term") )
                          , Pexp_constraint
                              ( Pexp_match
                                  ( Pexp_var "t"
                                  , [ { pc_lhs =
                                          Ppat_construct
                                            ("Int", Some ([], Ppat_var "x"))
                                      ; pc_rhs = Pexp_var "x"
                                      }
                                    ; { pc_lhs =
                                          Ppat_construct
                                            ("Bool", Some ([], Ppat_var "x"))
                                      ; pc_rhs = Pexp_var "x"
                                      }
                                    ; { pc_lhs =
                                          Ppat_construct
                                            ("Succ", Some ([], Ppat_var "t"))
                                      ; pc_rhs =
                                          Pexp_app
                                            ( Pexp_app
                                                ( Pexp_prim Prim_add
                                                , Pexp_app
                                                    ( Pexp_var "eval"
                                                    , Pexp_var "t" ) )
                                            , Pexp_const (Const_int 1) )
                                      }
                                    ; { pc_lhs =
                                          Ppat_construct
                                            ( "If"
                                            , Some
                                                ( []
                                                , Ppat_tuple
                                                    [ Ppat_var "t1"
                                                    ; Ppat_var "t2"
                                                    ; Ppat_var "t3"
                                                    ] ) )
                                      ; pc_rhs =
                                          Pexp_ifthenelse
                                            ( Pexp_app
                                                (Pexp_var "eval", Pexp_var "t1")
                                            , Pexp_app
                                                (Pexp_var "eval", Pexp_var "t2")
                                            , Pexp_app
                                                (Pexp_var "eval", Pexp_var "t3")
                                            )
                                      }
                                    ; { pc_lhs =
                                          Ppat_construct
                                            ( "Pair"
                                            , Some
                                                ( []
                                                , Ppat_tuple
                                                    [ Ppat_var "t1"
                                                    ; Ppat_var "t2"
                                                    ] ) )
                                      ; pc_rhs =
                                          Pexp_tuple
                                            [ Pexp_app
                                                (Pexp_var "eval", Pexp_var "t1")
                                            ; Pexp_app
                                                (Pexp_var "eval", Pexp_var "t2")
                                            ]
                                      }
                                    ; { pc_lhs =
                                          Ppat_construct
                                            ("Fst", Some ([], Ppat_var "t"))
                                      ; pc_rhs =
                                          Pexp_app
                                            ( Pexp_var "fst"
                                            , Pexp_app
                                                (Pexp_var "eval", Pexp_var "t")
                                            )
                                      }
                                    ; { pc_lhs =
                                          Ppat_construct
                                            ("Snd", Some ([], Ppat_var "t"))
                                      ; pc_rhs =
                                          Pexp_app
                                            ( Pexp_var "snd"
                                            , Pexp_app
                                                (Pexp_var "eval", Pexp_var "t")
                                            )
                                      }
                                    ] )
                              , Ptyp_var "a" ) )
                    }
                  ]
                , Pexp_const Const_unit )))
  in
  (* print_constraint_result ~env exp; *)
  print_infer_result ~debug:false ~env exp;
  [%expect
    {|
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Constructor: unit
       └──Desc: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Tuple
                         └──Type expr: Variable: 3
                         └──Type expr: Variable: 6
                      └──Type expr: Variable: 3
                   └──Desc: Variable: fst
                └──Abstraction:
                   └──Variables: 6,3,3
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Tuple
                            └──Type expr: Variable: 3
                            └──Type expr: Variable: 6
                         └──Type expr: Variable: 3
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Tuple
                               └──Type expr: Variable: 3
                               └──Type expr: Variable: 6
                            └──Desc: Tuple
                               └──Pattern:
                                  └──Type expr: Variable: 3
                                  └──Desc: Variable: x
                               └──Pattern:
                                  └──Type expr: Variable: 6
                                  └──Desc: Any
                         └──Expression:
                            └──Type expr: Variable: 3
                            └──Desc: Variable
                               └──Variable: x
          └──Expression:
             └──Type expr: Constructor: unit
             └──Desc: Let
                └──Value bindings:
                   └──Value binding:
                      └──Pattern:
                         └──Type expr: Arrow
                            └──Type expr: Tuple
                               └──Type expr: Variable: 16
                               └──Type expr: Variable: 12
                            └──Type expr: Variable: 12
                         └──Desc: Variable: snd
                      └──Abstraction:
                         └──Variables: 12,16,12
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Tuple
                                  └──Type expr: Variable: 16
                                  └──Type expr: Variable: 12
                               └──Type expr: Variable: 12
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: 16
                                     └──Type expr: Variable: 12
                                  └──Desc: Tuple
                                     └──Pattern:
                                        └──Type expr: Variable: 16
                                        └──Desc: Any
                                     └──Pattern:
                                        └──Type expr: Variable: 12
                                        └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Variable: 12
                                  └──Desc: Variable
                                     └──Variable: x
                └──Expression:
                   └──Type expr: Constructor: unit
                   └──Desc: Let rec
                      └──Value bindings:
                         └──Value binding:
                            └──Variable: eval
                            └──Abstraction:
                               └──Variables: 23
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: 40
                                     └──Type expr: Variable: 40
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: term
                                           └──Type expr: Variable: 40
                                        └──Desc: Variable: t
                                     └──Expression:
                                        └──Type expr: Variable: 40
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 40
                                              └──Desc: Variable
                                                 └──Variable: t
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: 40
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 40
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Int
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 40
                                                       └──Pattern:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable: x
                                                 └──Expression:
                                                    └──Type expr: Variable: 40
                                                    └──Desc: Variable
                                                       └──Variable: x
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 40
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Bool
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: bool
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 40
                                                       └──Pattern:
                                                          └──Type expr: Constructor: bool
                                                          └──Desc: Variable: x
                                                 └──Expression:
                                                    └──Type expr: Variable: 40
                                                    └──Desc: Variable
                                                       └──Variable: x
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 40
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Constructor: int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 40
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Constructor: int
                                                          └──Desc: Variable: t
                                                 └──Expression:
                                                    └──Type expr: Variable: 40
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Variable: 40
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: int
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: int
                                                                      └──Type expr: Variable: 40
                                                                └──Desc: Primitive: (+)
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Constructor: int
                                                                         └──Type expr: Constructor: int
                                                                      └──Desc: Variable
                                                                         └──Variable: eval
                                                                         └──Type expr: Constructor: int
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Constructor: int
                                                                      └──Desc: Variable
                                                                         └──Variable: t
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Constant: 1
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 40
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: If
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Constructor: bool
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 40
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 40
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 40
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Constructor: bool
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 40
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 40
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Constructor: bool
                                                                └──Desc: Variable: t1
                                                             └──Pattern:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 40
                                                                └──Desc: Variable: t2
                                                             └──Pattern:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 40
                                                                └──Desc: Variable: t3
                                                 └──Expression:
                                                    └──Type expr: Variable: 40
                                                    └──Desc: If
                                                       └──Expression:
                                                          └──Type expr: Constructor: bool
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Constructor: bool
                                                                   └──Type expr: Constructor: bool
                                                                └──Desc: Variable
                                                                   └──Variable: eval
                                                                   └──Type expr: Constructor: bool
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Constructor: bool
                                                                └──Desc: Variable
                                                                   └──Variable: t1
                                                       └──Expression:
                                                          └──Type expr: Variable: 40
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 40
                                                                   └──Type expr: Variable: 40
                                                                └──Desc: Variable
                                                                   └──Variable: eval
                                                                   └──Type expr: Variable: 40
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 40
                                                                └──Desc: Variable
                                                                   └──Variable: t2
                                                       └──Expression:
                                                          └──Type expr: Variable: 40
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 40
                                                                   └──Type expr: Variable: 40
                                                                └──Desc: Variable
                                                                   └──Variable: eval
                                                                   └──Type expr: Variable: 40
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 40
                                                                └──Desc: Variable
                                                                   └──Variable: t3
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 40
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Pair
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 168
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 166
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 40
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 168
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 166
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 168
                                                                └──Desc: Variable: t1
                                                             └──Pattern:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 166
                                                                └──Desc: Variable: t2
                                                 └──Expression:
                                                    └──Type expr: Variable: 40
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Variable: 168
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 168
                                                                   └──Type expr: Variable: 168
                                                                └──Desc: Variable
                                                                   └──Variable: eval
                                                                   └──Type expr: Variable: 168
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 168
                                                                └──Desc: Variable
                                                                   └──Variable: t1
                                                       └──Expression:
                                                          └──Type expr: Variable: 166
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 166
                                                                   └──Type expr: Variable: 166
                                                                └──Desc: Variable
                                                                   └──Variable: eval
                                                                   └──Type expr: Variable: 166
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 166
                                                                └──Desc: Variable
                                                                   └──Variable: t2
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 40
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fst
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 208
                                                                   └──Type expr: Variable: 209
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 40
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 208
                                                                └──Type expr: Variable: 209
                                                          └──Desc: Variable: t
                                                 └──Expression:
                                                    └──Type expr: Variable: 40
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 40
                                                                └──Type expr: Variable: 209
                                                             └──Type expr: Variable: 40
                                                          └──Desc: Variable
                                                             └──Variable: fst
                                                             └──Type expr: Variable: 209
                                                             └──Type expr: Variable: 40
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 40
                                                             └──Type expr: Variable: 209
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 40
                                                                         └──Type expr: Variable: 209
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 40
                                                                      └──Type expr: Variable: 209
                                                                └──Desc: Variable
                                                                   └──Variable: eval
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 40
                                                                      └──Type expr: Variable: 209
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 40
                                                                      └──Type expr: Variable: 209
                                                                └──Desc: Variable
                                                                   └──Variable: t
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 40
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Snd
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 242
                                                                   └──Type expr: Variable: 243
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 40
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 242
                                                                └──Type expr: Variable: 243
                                                          └──Desc: Variable: t
                                                 └──Expression:
                                                    └──Type expr: Variable: 40
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 242
                                                                └──Type expr: Variable: 40
                                                             └──Type expr: Variable: 40
                                                          └──Desc: Variable
                                                             └──Variable: snd
                                                             └──Type expr: Variable: 40
                                                             └──Type expr: Variable: 242
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 242
                                                             └──Type expr: Variable: 40
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 242
                                                                         └──Type expr: Variable: 40
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 242
                                                                      └──Type expr: Variable: 40
                                                                └──Desc: Variable
                                                                   └──Variable: eval
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 242
                                                                      └──Type expr: Variable: 40
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 242
                                                                      └──Type expr: Variable: 40
                                                                └──Desc: Variable
                                                                   └──Variable: t
                      └──Expression:
                         └──Type expr: Constructor: unit
                         └──Desc: Constant: () |}]


let add_boxed_id env =
  let name = "boxed_id" in
  let alphas = [] in
  let type_ = Type_expr.make (Ttyp_constr ([], name)) in
  let a = Type_var.make () in
  let a' = Type_expr.make (Ttyp_var a) in
  Env.add_type_decl
    env
    { type_name = name
    ; type_kind =
        Type_record
          [ { label_name = "f"
            ; label_alphas = alphas
            ; label_betas = [ a ]
            ; label_arg = Type_expr.make (Ttyp_arrow (a', a'))
            ; label_type = type_
            }
          ]
    }


let%expect_test "semi-explicit first-class poly-1" =
  let env = add_boxed_id Env.empty in
  let exp =
    Pexp_let
      ( Nonrecursive
      , [ { pvb_forall_vars = []
          ; pvb_pat = Ppat_var "id"
          ; pvb_expr =
              Pexp_record [ "f", Pexp_fun (Ppat_var "x", Pexp_var "x") ]
          }
        ]
      , let f = Pexp_field (Pexp_var "id", "f") in
        Pexp_tuple
          [ Pexp_app (f, Pexp_const (Const_int 1))
          ; Pexp_app (f, Pexp_const (Const_bool true))
          ] )
  in
  print_infer_result ~env exp;
  [%expect
    {|
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Tuple
          └──Type expr: Constructor: int
          └──Type expr: Constructor: bool
       └──Desc: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: boxed_id
                   └──Desc: Variable: id
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: boxed_id
                      └──Desc: Record
                         └──Label description:
                            └──Label: f
                            └──Label argument type:
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 5
                                  └──Type expr: Variable: 5
                            └──Label type:
                               └──Type expr: Constructor: boxed_id
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: 5
                               └──Type expr: Variable: 5
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: 5
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Variable: 5
                                  └──Desc: Variable
                                     └──Variable: x
          └──Expression:
             └──Type expr: Tuple
                └──Type expr: Constructor: int
                └──Type expr: Constructor: bool
             └──Desc: Tuple
                └──Expression:
                   └──Type expr: Constructor: int
                   └──Desc: Application
                      └──Expression:
                         └──Type expr: Arrow
                            └──Type expr: Constructor: int
                            └──Type expr: Constructor: int
                         └──Desc: Field
                            └──Expression:
                               └──Type expr: Constructor: boxed_id
                               └──Desc: Variable
                                  └──Variable: id
                            └──Label description:
                               └──Label: f
                               └──Label argument type:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: int
                               └──Label type:
                                  └──Type expr: Constructor: boxed_id
                      └──Expression:
                         └──Type expr: Constructor: int
                         └──Desc: Constant: 1
                └──Expression:
                   └──Type expr: Constructor: bool
                   └──Desc: Application
                      └──Expression:
                         └──Type expr: Arrow
                            └──Type expr: Constructor: bool
                            └──Type expr: Constructor: bool
                         └──Desc: Field
                            └──Expression:
                               └──Type expr: Constructor: boxed_id
                               └──Desc: Variable
                                  └──Variable: id
                            └──Label description:
                               └──Label: f
                               └──Label argument type:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: bool
                                     └──Type expr: Constructor: bool
                               └──Label type:
                                  └──Type expr: Constructor: boxed_id
                      └──Expression:
                         └──Type expr: Constructor: bool
                         └──Desc: Constant: true |}]


let add_tree env =
  let name = "tree" in
  let a = Type_var.make () in
  let params = [ a ]
  and a' = Type_expr.make (Ttyp_var a) in
  let type_ = Type_expr.make (Ttyp_constr ([ a' ], name)) in
  Env.add_type_decl
    env
    { type_name = name
    ; type_kind =
        Type_variant
          [ { constructor_name = "Empty_tree"
            ; constructor_alphas = params
            ; constructor_arg = None
            ; constructor_type = type_
            ; constructor_constraints = []
            }
          ; { constructor_name = "Node"
            ; constructor_alphas = params
            ; constructor_arg =
                Some
                  { constructor_arg_betas = []
                  ; constructor_arg_type =
                      Type_expr.make (Ttyp_tuple [ a'; type_; a' ])
                  }
            ; constructor_type = type_
            ; constructor_constraints = []
            }
          ]
    }


let add_option env =
  let name = "option" in
  let a = Type_var.make () in
  let params = [ a ]
  and a' = Type_expr.make (Ttyp_var a) in
  let type_ = Type_expr.make (Ttyp_constr ([ a' ], name)) in
  Env.add_type_decl
    env
    { type_name = name
    ; type_kind =
        Type_variant
          [ { constructor_name = "None"
            ; constructor_alphas = params
            ; constructor_arg = None
            ; constructor_type = type_
            ; constructor_constraints = []
            }
          ; { constructor_name = "Some"
            ; constructor_alphas = params
            ; constructor_arg =
                Some { constructor_arg_betas = []; constructor_arg_type = a' }
            ; constructor_type = type_
            ; constructor_constraints = []
            }
          ]
    }


let%expect_test "is even, is odd" =
  let exp =
    {| 
         let rec is_even = fun n -> 
            if n = 0 then true else is_odd (n - 1)
         and is_odd = fun n -> 
            if n = 1 then true else is_even (n - 1)
         in ()
      |}
  in
  print_infer_result' ~env:Env.empty exp;
  [%expect
    {|
     Variables:
     Expression:
     └──Expression:
        └──Type expr: Constructor: unit
        └──Desc: Let rec
           └──Value bindings:
              └──Value binding:
                 └──Variable: is_odd
                 └──Abstraction:
                    └──Variables:
                    └──Expression:
                       └──Type expr: Arrow
                          └──Type expr: Constructor: int
                          └──Type expr: Constructor: bool
                       └──Desc: Function
                          └──Pattern:
                             └──Type expr: Constructor: int
                             └──Desc: Variable: n
                          └──Expression:
                             └──Type expr: Constructor: bool
                             └──Desc: If
                                └──Expression:
                                   └──Type expr: Constructor: bool
                                   └──Desc: Application
                                      └──Expression:
                                         └──Type expr: Arrow
                                            └──Type expr: Constructor: int
                                            └──Type expr: Constructor: bool
                                         └──Desc: Application
                                            └──Expression:
                                               └──Type expr: Arrow
                                                  └──Type expr: Constructor: int
                                                  └──Type expr: Arrow
                                                     └──Type expr: Constructor: int
                                                     └──Type expr: Constructor: bool
                                               └──Desc: Primitive: (=)
                                            └──Expression:
                                               └──Type expr: Constructor: int
                                               └──Desc: Variable
                                                  └──Variable: n
                                      └──Expression:
                                         └──Type expr: Constructor: int
                                         └──Desc: Constant: 0
                                └──Expression:
                                   └──Type expr: Constructor: bool
                                   └──Desc: Constant: true
                                └──Expression:
                                   └──Type expr: Constructor: bool
                                   └──Desc: Application
                                      └──Expression:
                                         └──Type expr: Arrow
                                            └──Type expr: Constructor: int
                                            └──Type expr: Constructor: bool
                                         └──Desc: Variable
                                            └──Variable: is_odd
                                      └──Expression:
                                         └──Type expr: Constructor: int
                                         └──Desc: Application
                                            └──Expression:
                                               └──Type expr: Arrow
                                                  └──Type expr: Constructor: int
                                                  └──Type expr: Constructor: int
                                               └──Desc: Application
                                                  └──Expression:
                                                     └──Type expr: Arrow
                                                        └──Type expr: Constructor: int
                                                        └──Type expr: Arrow
                                                           └──Type expr: Constructor: int
                                                           └──Type expr: Constructor: int
                                                     └──Desc: Primitive: (-)
                                                  └──Expression:
                                                     └──Type expr: Constructor: int
                                                     └──Desc: Variable
                                                        └──Variable: n
                                            └──Expression:
                                               └──Type expr: Constructor: int
                                               └──Desc: Constant: 1
              └──Value binding:
                 └──Variable: is_even
                 └──Abstraction:
                    └──Variables:
                    └──Expression:
                       └──Type expr: Arrow
                          └──Type expr: Constructor: int
                          └──Type expr: Constructor: bool
                       └──Desc: Function
                          └──Pattern:
                             └──Type expr: Constructor: int
                             └──Desc: Variable: n
                          └──Expression:
                             └──Type expr: Constructor: bool
                             └──Desc: If
                                └──Expression:
                                   └──Type expr: Constructor: bool
                                   └──Desc: Application
                                      └──Expression:
                                         └──Type expr: Arrow
                                            └──Type expr: Constructor: int
                                            └──Type expr: Constructor: bool
                                         └──Desc: Application
                                            └──Expression:
                                               └──Type expr: Arrow
                                                  └──Type expr: Constructor: int
                                                  └──Type expr: Arrow
                                                     └──Type expr: Constructor: int
                                                     └──Type expr: Constructor: bool
                                               └──Desc: Primitive: (=)
                                            └──Expression:
                                               └──Type expr: Constructor: int
                                               └──Desc: Variable
                                                  └──Variable: n
                                      └──Expression:
                                         └──Type expr: Constructor: int
                                         └──Desc: Constant: 1
                                └──Expression:
                                   └──Type expr: Constructor: bool
                                   └──Desc: Constant: true
                                └──Expression:
                                   └──Type expr: Constructor: bool
                                   └──Desc: Application
                                      └──Expression:
                                         └──Type expr: Arrow
                                            └──Type expr: Constructor: int
                                            └──Type expr: Constructor: bool
                                         └──Desc: Variable
                                            └──Variable: is_even
                                      └──Expression:
                                         └──Type expr: Constructor: int
                                         └──Desc: Application
                                            └──Expression:
                                               └──Type expr: Arrow
                                                  └──Type expr: Constructor: int
                                                  └──Type expr: Constructor: int
                                               └──Desc: Application
                                                  └──Expression:
                                                     └──Type expr: Arrow
                                                        └──Type expr: Constructor: int
                                                        └──Type expr: Arrow
                                                           └──Type expr: Constructor: int
                                                           └──Type expr: Constructor: int
                                                     └──Desc: Primitive: (-)
                                                  └──Expression:
                                                     └──Type expr: Constructor: int
                                                     └──Desc: Variable
                                                        └──Variable: n
                                            └──Expression:
                                               └──Type expr: Constructor: int
                                               └──Desc: Constant: 1
           └──Expression:
              └──Type expr: Constructor: unit
              └──Desc: Constant: () |}]
