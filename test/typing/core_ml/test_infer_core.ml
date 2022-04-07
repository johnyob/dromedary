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
    Format.fprintf ppf "Variables: %s@." (String.concat ~sep:"," variables);
    Typedtree.pp_expression_mach ppf texp
  | Error err -> Sexp.to_string_hum err |> print_endline


let add_list env =
  let name = "list" in
  let params = [ "a" ] in
  let a = make_type_expr (Ttyp_var "a") in
  let type_ = make_type_expr (Ttyp_constr ([ a ], name)) in
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
                      make_type_expr (Ttyp_tuple [ a; type_ ])
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
    Variables: a1775,a1775
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Variable: a1775
          └──Type expr: Variable: a1775
       └──Desc: Function
          └──Pattern:
             └──Type expr: Variable: a1775
             └──Desc: Variable: x
          └──Expression:
             └──Type expr: Variable: a1775
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
    Variables: a1788
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Arrow
             └──Type expr: Tuple
                └──Type expr: Variable: a1794
                └──Type expr: Variable: a1795
             └──Type expr: Variable: a1788
          └──Type expr: Arrow
             └──Type expr: Variable: a1794
             └──Type expr: Arrow
                └──Type expr: Variable: a1795
                └──Type expr: Variable: a1788
       └──Desc: Function
          └──Pattern:
             └──Type expr: Arrow
                └──Type expr: Tuple
                   └──Type expr: Variable: a1794
                   └──Type expr: Variable: a1795
                └──Type expr: Variable: a1788
             └──Desc: Variable: f
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Variable: a1794
                └──Type expr: Arrow
                   └──Type expr: Variable: a1795
                   └──Type expr: Variable: a1788
             └──Desc: Function
                └──Pattern:
                   └──Type expr: Variable: a1794
                   └──Desc: Variable: x
                └──Expression:
                   └──Type expr: Arrow
                      └──Type expr: Variable: a1795
                      └──Type expr: Variable: a1788
                   └──Desc: Function
                      └──Pattern:
                         └──Type expr: Variable: a1795
                         └──Desc: Variable: y
                      └──Expression:
                         └──Type expr: Variable: a1788
                         └──Desc: Application
                            └──Expression:
                               └──Type expr: Arrow
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: a1794
                                     └──Type expr: Variable: a1795
                                  └──Type expr: Variable: a1788
                               └──Desc: Variable
                                  └──Variable: f
                            └──Expression:
                               └──Type expr: Tuple
                                  └──Type expr: Variable: a1794
                                  └──Type expr: Variable: a1795
                               └──Desc: Tuple
                                  └──Expression:
                                     └──Type expr: Variable: a1794
                                     └──Desc: Variable
                                        └──Variable: x
                                  └──Expression:
                                     └──Type expr: Variable: a1795
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
    Variables: a1804,a1814,a1811,a1811,a1814
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Arrow
             └──Type expr: Variable: a1814
             └──Type expr: Arrow
                └──Type expr: Variable: a1811
                └──Type expr: Variable: a1804
          └──Type expr: Arrow
             └──Type expr: Tuple
                └──Type expr: Variable: a1814
                └──Type expr: Variable: a1811
             └──Type expr: Variable: a1804
       └──Desc: Function
          └──Pattern:
             └──Type expr: Arrow
                └──Type expr: Variable: a1814
                └──Type expr: Arrow
                   └──Type expr: Variable: a1811
                   └──Type expr: Variable: a1804
             └──Desc: Variable: f
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Tuple
                   └──Type expr: Variable: a1814
                   └──Type expr: Variable: a1811
                └──Type expr: Variable: a1804
             └──Desc: Function
                └──Pattern:
                   └──Type expr: Tuple
                      └──Type expr: Variable: a1814
                      └──Type expr: Variable: a1811
                   └──Desc: Tuple
                      └──Pattern:
                         └──Type expr: Variable: a1814
                         └──Desc: Variable: x
                      └──Pattern:
                         └──Type expr: Variable: a1811
                         └──Desc: Variable: y
                └──Expression:
                   └──Type expr: Variable: a1804
                   └──Desc: Application
                      └──Expression:
                         └──Type expr: Arrow
                            └──Type expr: Variable: a1811
                            └──Type expr: Variable: a1804
                         └──Desc: Application
                            └──Expression:
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a1814
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a1811
                                     └──Type expr: Variable: a1804
                               └──Desc: Variable
                                  └──Variable: f
                            └──Expression:
                               └──Type expr: Variable: a1814
                               └──Desc: Variable
                                  └──Variable: x
                      └──Expression:
                         └──Type expr: Variable: a1811
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
    Variables: a1827
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Arrow
             └──Type expr: Variable: a1830
             └──Type expr: Variable: a1827
          └──Type expr: Arrow
             └──Type expr: Arrow
                └──Type expr: Variable: a1833
                └──Type expr: Variable: a1830
             └──Type expr: Arrow
                └──Type expr: Variable: a1833
                └──Type expr: Variable: a1827
       └──Desc: Function
          └──Pattern:
             └──Type expr: Arrow
                └──Type expr: Variable: a1830
                └──Type expr: Variable: a1827
             └──Desc: Variable: f
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Arrow
                   └──Type expr: Variable: a1833
                   └──Type expr: Variable: a1830
                └──Type expr: Arrow
                   └──Type expr: Variable: a1833
                   └──Type expr: Variable: a1827
             └──Desc: Function
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: a1833
                      └──Type expr: Variable: a1830
                   └──Desc: Variable: g
                └──Expression:
                   └──Type expr: Arrow
                      └──Type expr: Variable: a1833
                      └──Type expr: Variable: a1827
                   └──Desc: Function
                      └──Pattern:
                         └──Type expr: Variable: a1833
                         └──Desc: Variable: x
                      └──Expression:
                         └──Type expr: Variable: a1827
                         └──Desc: Application
                            └──Expression:
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a1830
                                  └──Type expr: Variable: a1827
                               └──Desc: Variable
                                  └──Variable: f
                            └──Expression:
                               └──Type expr: Variable: a1830
                               └──Desc: Application
                                  └──Expression:
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: a1833
                                        └──Type expr: Variable: a1830
                                     └──Desc: Variable
                                        └──Variable: g
                                  └──Expression:
                                     └──Type expr: Variable: a1833
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
    Variables: a1841,a1838,a1838
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Tuple
             └──Type expr: Variable: a1838
             └──Type expr: Variable: a1841
          └──Type expr: Variable: a1838
       └──Desc: Function
          └──Pattern:
             └──Type expr: Tuple
                └──Type expr: Variable: a1838
                └──Type expr: Variable: a1841
             └──Desc: Tuple
                └──Pattern:
                   └──Type expr: Variable: a1838
                   └──Desc: Variable: x
                └──Pattern:
                   └──Type expr: Variable: a1841
                   └──Desc: Variable: y
          └──Expression:
             └──Type expr: Variable: a1838
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
    Variables: a1847,a1851,a1847
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Tuple
             └──Type expr: Variable: a1851
             └──Type expr: Variable: a1847
          └──Type expr: Variable: a1847
       └──Desc: Function
          └──Pattern:
             └──Type expr: Tuple
                └──Type expr: Variable: a1851
                └──Type expr: Variable: a1847
             └──Desc: Tuple
                └──Pattern:
                   └──Type expr: Variable: a1851
                   └──Desc: Variable: x
                └──Pattern:
                   └──Type expr: Variable: a1847
                   └──Desc: Variable: y
          └──Expression:
             └──Type expr: Variable: a1847
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
    Variables: a1856,a1856
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Constructor: list
             └──Type expr: Variable: a1859
          └──Type expr: Variable: a1856
       └──Desc: Function
          └──Pattern:
             └──Type expr: Constructor: list
                └──Type expr: Variable: a1859
             └──Desc: Construct
                └──Constructor description:
                   └──Name: Cons
                   └──Constructor argument type:
                      └──Type expr: Tuple
                         └──Type expr: Variable: a1859
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a1859
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a1859
                └──Pattern:
                   └──Type expr: Tuple
                      └──Type expr: Variable: a1859
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a1859
                   └──Desc: Tuple
                      └──Pattern:
                         └──Type expr: Variable: a1859
                         └──Desc: Variable: x
                      └──Pattern:
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a1859
                         └──Desc: Any
          └──Expression:
             └──Type expr: Variable: a1856
             └──Desc: Variable
                └──Variable: x
                └──Type expr: Variable: a1856 |}]

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
    Variables: a1874,a1874,a1874
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Variable: a1874
          └──Type expr: Variable: a1874
       └──Desc: Function
          └──Pattern:
             └──Type expr: Variable: a1874
             └──Desc: Variable: x
          └──Expression:
             └──Type expr: Variable: a1874
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
          └──Type expr: Variable: a1888
          └──Type expr: Variable: a1888
       └──Desc: Function
          └──Pattern:
             └──Type expr: Variable: a1883
             └──Desc: Variable: x
          └──Expression:
             └──Type expr: Variable: a1883
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
    ("Cannot unify types" (type_expr1 ((desc (Ttyp_constr (() int)))))
     (type_expr2 ((desc (Ttyp_var a48))))) |}]

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
                      └──Type expr: Variable: a1941
                      └──Type expr: Variable: a1941
                   └──Desc: Variable: id
                └──Abstraction:
                   └──Variables: a1941,a1941
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a1941
                         └──Type expr: Variable: a1941
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a1941
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: a1941
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
                   └──Variables: a1984,a1995
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: a1995
                            └──Type expr: Variable: a1984
                         └──Type expr: Arrow
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a1995
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a1984
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a1995
                               └──Type expr: Variable: a1984
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a1995
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a1984
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: a1995
                                  └──Desc: Variable: xs
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: a1984
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Variable: a1995
                                        └──Desc: Variable
                                           └──Variable: xs
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: a1995
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a1995
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a1995
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a1984
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a1984
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a1995
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a1995
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a1995
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a1995
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a1995
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a1995
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Variable: a1995
                                                          └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a1995
                                                          └──Desc: Variable: xs
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a1984
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a1984
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a1984
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a1984
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a1984
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a1984
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Variable: a1984
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: a1995
                                                                   └──Type expr: Variable: a1984
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Variable: a1995
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a1984
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: a1995
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: a1984
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Variable: a1995
                                                                            └──Type expr: Variable: a1984
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Variable: a1995
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Variable: a1984
                                                                      └──Desc: Variable
                                                                         └──Variable: map
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: a1995
                                                                         └──Type expr: Variable: a1984
                                                                      └──Desc: Variable
                                                                         └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: a1995
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
    Variables: a2183
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Variable: a2183
          └──Type expr: Constructor: int
       └──Desc: Let rec
          └──Value bindings:
             └──Value binding:
                └──Variable: bar
                └──Abstraction:
                   └──Variables: a2176
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a2170
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a2170
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Constant: 1
             └──Value binding:
                └──Variable: foo
                └──Abstraction:
                   └──Variables: a2170
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a2176
                         └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a2176
                            └──Desc: Variable: y
                         └──Expression:
                            └──Type expr: Constructor: bool
                            └──Desc: Constant: true
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Variable: a2183
                └──Type expr: Constructor: int
             └──Desc: Variable
                └──Variable: foo
                └──Type expr: Variable: a2183 |}]

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
    Variables: a2197,a2197
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
                                  └──Type expr: Variable: a2197
                                  └──Type expr: Variable: a2197
                               └──Type expr: Constructor: unit
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a2197
                                     └──Type expr: Variable: a2197
                                  └──Desc: Variable: f
                               └──Expression:
                                  └──Type expr: Constructor: unit
                                  └──Desc: Constant: ()
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a2197
                               └──Type expr: Variable: a2197
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: a2197
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Variable: a2197
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
    Variables: a2238
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Variable: a2238
          └──Type expr: Variable: a2238
       └──Desc: Let rec
          └──Value bindings:
             └──Value binding:
                └──Variable: id
                └──Abstraction:
                   └──Variables: a2203
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a2227
                         └──Type expr: Variable: a2227
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a2227
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: a2227
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
                └──Type expr: Variable: a2238
                └──Type expr: Variable: a2238
             └──Desc: Variable
                └──Variable: id
                └──Type expr: Variable: a2238 |}]

let add_eq env =
  let name = "eq" in
  let params = [ "a"; "b" ] in
  let a = make_type_expr (Ttyp_var "a")
  and b = make_type_expr (Ttyp_var "b") in
  let type_ = make_type_expr (Ttyp_constr ([ a; b ], name)) in
  Env.add_type_decl
    env
    { type_name = name
    ; type_kind =
        Type_variant
          [ { constructor_name = "Refl"
            ; constructor_alphas = params
            ; constructor_arg = None
            ; constructor_type = type_
            ; constructor_constraints = [ a, b ]
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
                         └──Type expr: Variable: a2252
                         └──Type expr: Constructor: int
                      └──Type expr: Constructor: int
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: a2252
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: a2252
                            └──Type expr: Constructor: int
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: a2252
                               └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: a2252
                                     └──Type expr: Constructor: int
                                  └──Desc: Variable
                                     └──Variable: x
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: a2252
                                  └──Type expr: Constructor: int
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: a2252
                                           └──Type expr: Constructor: int
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Refl
                                              └──Constructor type:
                                                 └──Type expr: Constructor: eq
                                                    └──Type expr: Variable: a2252
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
                         └──Type expr: Variable: a2281
                         └──Type expr: Constructor: int
                      └──Type expr: Constructor: bool
                   └──Desc: Variable: f1
                └──Abstraction:
                   └──Variables: a2281
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: a2281
                            └──Type expr: Constructor: int
                         └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: a2281
                               └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: bool
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: a2281
                                     └──Type expr: Constructor: int
                                  └──Desc: Variable
                                     └──Variable: x
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: a2281
                                  └──Type expr: Constructor: int
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: a2281
                                           └──Type expr: Constructor: int
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Refl
                                              └──Constructor type:
                                                 └──Type expr: Constructor: eq
                                                    └──Type expr: Variable: a2281
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
                         └──Type expr: Variable: a2310
                         └──Type expr: Constructor: int
                      └──Type expr: Arrow
                         └──Type expr: Variable: a2310
                         └──Type expr: Constructor: bool
                   └──Desc: Variable: f2
                └──Abstraction:
                   └──Variables: a2310
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: a2310
                            └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Variable: a2310
                            └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: a2310
                               └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a2310
                               └──Type expr: Constructor: bool
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: a2310
                                  └──Desc: Variable: y
                               └──Expression:
                                  └──Type expr: Constructor: bool
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: a2310
                                           └──Type expr: Constructor: int
                                        └──Desc: Variable
                                           └──Variable: x
                                     └──Type expr: Constructor: eq
                                        └──Type expr: Variable: a2310
                                        └──Type expr: Constructor: int
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a2310
                                                 └──Type expr: Constructor: int
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Refl
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a2310
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
                                                             └──Type expr: Variable: a2310
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: int
                                                                └──Type expr: Constructor: bool
                                                          └──Desc: Primitive: (=)
                                                       └──Expression:
                                                          └──Type expr: Variable: a2310
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
                         └──Type expr: Variable: a2364
                         └──Type expr: Constructor: int
                      └──Type expr: Arrow
                         └──Type expr: Variable: a2364
                         └──Type expr: Variable: a2364
                   └──Desc: Variable: g
                └──Abstraction:
                   └──Variables: a2364
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: a2364
                            └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Variable: a2364
                            └──Type expr: Variable: a2364
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: a2364
                               └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a2364
                               └──Type expr: Variable: a2364
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: a2364
                                  └──Desc: Variable: y
                               └──Expression:
                                  └──Type expr: Variable: a2364
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: a2364
                                           └──Type expr: Constructor: int
                                        └──Desc: Variable
                                           └──Variable: x
                                     └──Type expr: Constructor: eq
                                        └──Type expr: Variable: a2364
                                        └──Type expr: Constructor: int
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a2364
                                                 └──Type expr: Constructor: int
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Refl
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a2364
                                                          └──Type expr: Constructor: int
                                           └──Expression:
                                              └──Type expr: Variable: a2364
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
                                                                   └──Type expr: Variable: a2364
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: int
                                                                      └──Type expr: Constructor: bool
                                                                └──Desc: Primitive: (=)
                                                             └──Expression:
                                                                └──Type expr: Variable: a2364
                                                                └──Desc: Variable
                                                                   └──Variable: y
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Constant: 0
                                                 └──Expression:
                                                    └──Type expr: Variable: a2364
                                                    └──Desc: Variable
                                                       └──Variable: y
                                                 └──Expression:
                                                    └──Type expr: Variable: a2364
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
                         └──Type expr: Variable: a2430
                         └──Type expr: Constructor: int
                      └──Type expr: Constructor: int
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: a2430
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: a2430
                            └──Type expr: Constructor: int
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: a2430
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
                                                    └──Type expr: Variable: a2430
                                                    └──Type expr: Constructor: int
                                                 └──Desc: Variable
                                                    └──Variable: x
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a2430
                                                 └──Type expr: Constructor: int
                                              └──Cases:
                                                 └──Case:
                                                    └──Pattern:
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a2430
                                                          └──Type expr: Constructor: int
                                                       └──Desc: Construct
                                                          └──Constructor description:
                                                             └──Name: Refl
                                                             └──Constructor type:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: a2430
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
                         └──Type expr: Variable: a2476
                         └──Type expr: Variable: a2477
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: a2476
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: a2477
                   └──Desc: Variable: coerce
                └──Abstraction:
                   └──Variables: a2476,a2477
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: a2476
                            └──Type expr: Variable: a2477
                         └──Type expr: Arrow
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: a2476
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: a2477
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: a2476
                               └──Type expr: Variable: a2477
                            └──Desc: Variable: eq
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: a2476
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: a2477
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: a2476
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: a2477
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: a2476
                                           └──Type expr: Variable: a2477
                                        └──Desc: Variable
                                           └──Variable: eq
                                     └──Type expr: Constructor: eq
                                        └──Type expr: Variable: a2476
                                        └──Type expr: Variable: a2477
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a2476
                                                 └──Type expr: Variable: a2477
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Refl
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a2476
                                                          └──Type expr: Variable: a2477
                                           └──Expression:
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Variable: a2477
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
    let open Types.Algebra.Type_former in
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
  let alphas = [ "a" ] in
  let a = make_type_expr (Ttyp_var "a") in
  let type_ = make_type_expr (Ttyp_constr ([ a ], name)) in
  let int = make_type_expr (Ttyp_constr ([], "int")) in
  let bool = make_type_expr (Ttyp_constr ([], "bool")) in
  let b1 = make_type_expr (Ttyp_var "b1") in
  let b2 = make_type_expr (Ttyp_var "b2") in
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
            ; constructor_constraints = [ a, int ]
            }
          ; { constructor_name = "Succ"
            ; constructor_alphas = alphas
            ; constructor_arg =
                Some
                  { constructor_arg_betas = []
                  ; constructor_arg_type =
                      make_type_expr (Ttyp_constr ([ int ], name))
                  }
            ; constructor_type = type_
            ; constructor_constraints = [ a, int ]
            }
          ; { constructor_name = "Bool"
            ; constructor_alphas = alphas
            ; constructor_arg =
                Some { constructor_arg_betas = []; constructor_arg_type = bool }
            ; constructor_type = type_
            ; constructor_constraints = [ a, bool ]
            }
          ; { constructor_name = "If"
            ; constructor_alphas = alphas
            ; constructor_arg =
                Some
                  { constructor_arg_betas = []
                  ; constructor_arg_type =
                      make_type_expr
                        (Ttyp_tuple
                           [ make_type_expr (Ttyp_constr ([ bool ], name))
                           ; make_type_expr (Ttyp_constr ([ a ], name))
                           ; make_type_expr (Ttyp_constr ([ a ], name))
                           ])
                  }
            ; constructor_type = type_
            ; constructor_constraints = []
            }
          ; { constructor_name = "Pair"
            ; constructor_alphas = alphas
            ; constructor_arg =
                Some
                  { constructor_arg_betas = [ "b1"; "b2" ]
                  ; constructor_arg_type =
                      make_type_expr
                        (Ttyp_tuple
                           [ make_type_expr (Ttyp_constr ([ b1 ], name))
                           ; make_type_expr (Ttyp_constr ([ b2 ], name))
                           ])
                  }
            ; constructor_type = type_
            ; constructor_constraints =
                [ a, make_type_expr (Ttyp_tuple [ b1; b2 ]) ]
            }
          ; { constructor_name = "Fst"
            ; constructor_alphas = alphas
            ; constructor_arg =
                Some
                  { constructor_arg_betas = [ "b1"; "b2" ]
                  ; constructor_arg_type =
                      make_type_expr
                        (Ttyp_constr
                           ([ make_type_expr (Ttyp_tuple [ b1; b2 ]) ], name))
                  }
            ; constructor_type = type_
            ; constructor_constraints = [ a, b1 ]
            }
          ; { constructor_name = "Snd"
            ; constructor_alphas = alphas
            ; constructor_arg =
                Some
                  { constructor_arg_betas = [ "b1"; "b2" ]
                  ; constructor_arg_type =
                      make_type_expr
                        (Ttyp_constr
                           ([ make_type_expr (Ttyp_tuple [ b1; b2 ]) ], name))
                  }
            ; constructor_type = type_
            ; constructor_constraints = [ a, b2 ]
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
                         └──Type expr: Variable: a2557
                         └──Type expr: Variable: a2560
                      └──Type expr: Variable: a2557
                   └──Desc: Variable: fst
                └──Abstraction:
                   └──Variables: a2560,a2557,a2557
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Tuple
                            └──Type expr: Variable: a2557
                            └──Type expr: Variable: a2560
                         └──Type expr: Variable: a2557
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Tuple
                               └──Type expr: Variable: a2557
                               └──Type expr: Variable: a2560
                            └──Desc: Tuple
                               └──Pattern:
                                  └──Type expr: Variable: a2557
                                  └──Desc: Variable: x
                               └──Pattern:
                                  └──Type expr: Variable: a2560
                                  └──Desc: Any
                         └──Expression:
                            └──Type expr: Variable: a2557
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
                               └──Type expr: Variable: a2570
                               └──Type expr: Variable: a2566
                            └──Type expr: Variable: a2566
                         └──Desc: Variable: snd
                      └──Abstraction:
                         └──Variables: a2566,a2570,a2566
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Tuple
                                  └──Type expr: Variable: a2570
                                  └──Type expr: Variable: a2566
                               └──Type expr: Variable: a2566
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: a2570
                                     └──Type expr: Variable: a2566
                                  └──Desc: Tuple
                                     └──Pattern:
                                        └──Type expr: Variable: a2570
                                        └──Desc: Any
                                     └──Pattern:
                                        └──Type expr: Variable: a2566
                                        └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Variable: a2566
                                  └──Desc: Variable
                                     └──Variable: x
                └──Expression:
                   └──Type expr: Constructor: unit
                   └──Desc: Let rec
                      └──Value bindings:
                         └──Value binding:
                            └──Variable: eval
                            └──Abstraction:
                               └──Variables: a2577
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: a2594
                                     └──Type expr: Variable: a2594
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: term
                                           └──Type expr: Variable: a2594
                                        └──Desc: Variable: t
                                     └──Expression:
                                        └──Type expr: Variable: a2594
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a2594
                                              └──Desc: Variable
                                                 └──Variable: t
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: a2594
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a2594
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Int
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a2594
                                                       └──Pattern:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable: x
                                                 └──Expression:
                                                    └──Type expr: Variable: a2594
                                                    └──Desc: Variable
                                                       └──Variable: x
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a2594
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Bool
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: bool
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a2594
                                                       └──Pattern:
                                                          └──Type expr: Constructor: bool
                                                          └──Desc: Variable: x
                                                 └──Expression:
                                                    └──Type expr: Variable: a2594
                                                    └──Desc: Variable
                                                       └──Variable: x
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a2594
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Constructor: int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a2594
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Constructor: int
                                                          └──Desc: Variable: t
                                                 └──Expression:
                                                    └──Type expr: Variable: a2594
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Variable: a2594
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: int
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: int
                                                                      └──Type expr: Variable: a2594
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
                                                       └──Type expr: Variable: a2594
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: If
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Constructor: bool
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a2594
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a2594
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a2594
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Constructor: bool
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a2594
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a2594
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Constructor: bool
                                                                └──Desc: Variable: t1
                                                             └──Pattern:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a2594
                                                                └──Desc: Variable: t2
                                                             └──Pattern:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a2594
                                                                └──Desc: Variable: t3
                                                 └──Expression:
                                                    └──Type expr: Variable: a2594
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
                                                          └──Type expr: Variable: a2594
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a2594
                                                                   └──Type expr: Variable: a2594
                                                                └──Desc: Variable
                                                                   └──Variable: eval
                                                                   └──Type expr: Variable: a2594
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a2594
                                                                └──Desc: Variable
                                                                   └──Variable: t2
                                                       └──Expression:
                                                          └──Type expr: Variable: a2594
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a2594
                                                                   └──Type expr: Variable: a2594
                                                                └──Desc: Variable
                                                                   └──Variable: eval
                                                                   └──Type expr: Variable: a2594
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a2594
                                                                └──Desc: Variable
                                                                   └──Variable: t3
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a2594
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Pair
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a2713
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a2711
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a2594
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a2713
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a2711
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a2713
                                                                └──Desc: Variable: t1
                                                             └──Pattern:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a2711
                                                                └──Desc: Variable: t2
                                                 └──Expression:
                                                    └──Type expr: Variable: a2594
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Variable: a2713
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a2713
                                                                   └──Type expr: Variable: a2713
                                                                └──Desc: Variable
                                                                   └──Variable: eval
                                                                   └──Type expr: Variable: a2713
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a2713
                                                                └──Desc: Variable
                                                                   └──Variable: t1
                                                       └──Expression:
                                                          └──Type expr: Variable: a2711
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a2711
                                                                   └──Type expr: Variable: a2711
                                                                └──Desc: Variable
                                                                   └──Variable: eval
                                                                   └──Type expr: Variable: a2711
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a2711
                                                                └──Desc: Variable
                                                                   └──Variable: t2
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a2594
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fst
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a2751
                                                                   └──Type expr: Variable: a2752
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a2594
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a2751
                                                                └──Type expr: Variable: a2752
                                                          └──Desc: Variable: t
                                                 └──Expression:
                                                    └──Type expr: Variable: a2594
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a2594
                                                                └──Type expr: Variable: a2752
                                                             └──Type expr: Variable: a2594
                                                          └──Desc: Variable
                                                             └──Variable: fst
                                                             └──Type expr: Variable: a2752
                                                             └──Type expr: Variable: a2594
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a2594
                                                             └──Type expr: Variable: a2752
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a2594
                                                                         └──Type expr: Variable: a2752
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a2594
                                                                      └──Type expr: Variable: a2752
                                                                └──Desc: Variable
                                                                   └──Variable: eval
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a2594
                                                                      └──Type expr: Variable: a2752
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a2594
                                                                      └──Type expr: Variable: a2752
                                                                └──Desc: Variable
                                                                   └──Variable: t
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a2594
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Snd
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a2783
                                                                   └──Type expr: Variable: a2784
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a2594
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a2783
                                                                └──Type expr: Variable: a2784
                                                          └──Desc: Variable: t
                                                 └──Expression:
                                                    └──Type expr: Variable: a2594
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a2783
                                                                └──Type expr: Variable: a2594
                                                             └──Type expr: Variable: a2594
                                                          └──Desc: Variable
                                                             └──Variable: snd
                                                             └──Type expr: Variable: a2594
                                                             └──Type expr: Variable: a2783
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a2783
                                                             └──Type expr: Variable: a2594
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a2783
                                                                         └──Type expr: Variable: a2594
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a2783
                                                                      └──Type expr: Variable: a2594
                                                                └──Desc: Variable
                                                                   └──Variable: eval
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a2783
                                                                      └──Type expr: Variable: a2594
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a2783
                                                                      └──Type expr: Variable: a2594
                                                                └──Desc: Variable
                                                                   └──Variable: t
                      └──Expression:
                         └──Type expr: Constructor: unit
                         └──Desc: Constant: () |}]

let add_boxed_id env =
  let name = "boxed_id" in
  let alphas = [] in
  let type_ = make_type_expr (Ttyp_constr ([], name)) in
  let a = make_type_expr (Ttyp_var "a") in
  Env.add_type_decl
    env
    { type_name = name
    ; type_kind =
        Type_record
          [ { label_name = "f"
            ; label_alphas = alphas
            ; label_betas = [ "a" ]
            ; label_arg = make_type_expr (Ttyp_arrow (a, a))
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
                                  └──Type expr: Variable: a2818
                                  └──Type expr: Variable: a2818
                            └──Label type:
                               └──Type expr: Constructor: boxed_id
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a2818
                               └──Type expr: Variable: a2818
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: a2818
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Variable: a2818
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
