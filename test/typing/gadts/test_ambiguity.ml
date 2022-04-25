open! Import
open Util

(* Tests from typing-gadts/amibguity.ml
   -------------------------------------
   Test count: 13/16

   3 tests are removed due to reliance 
   on modules.
*)

let%expect_test "ambiguity-1" =
  let str =
    {|
      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;

      let (type 'a 'b) ret_e1 = 
        fun (if_ : bool) (eq : ('a, 'b) eq) (x : 'a) (y : 'b) -> 
          match eq with
          ( Refl -> if if_ then x else y
          | _ -> x
          )
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    ("Type escape it's equational scope"
     ("Type_expr.decode type_expr" (Type 30411 (Var 30411)))) |}]

let%expect_test "ambiguity-2" =
  let str =
    {|
      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;

      let (type 'a 'b) ret_e2 = 
        fun (if_ : bool) (eq : ('a, 'b) eq) (x : 'a) (y : 'b) ->
          match eq with
          ( Refl -> if if_ then x else y
          | _ -> y
          )
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    ("Type escape it's equational scope"
     ("Type_expr.decode type_expr" (Type 30462 (Var 30462)))) |}]

let%expect_test "ambiguity-3" =
  let str =
    {|
      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;

  
      let (type 'a) ret_ei1 = 
        (* [ret_ei2] is identical? *)
        fun (if_ : bool) (eq : ('a, int) eq) (x : 'a) ->
          match eq with
          ( Refl -> if if_ then x else 0
          | _ -> x
          )
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    ("Type escape it's equational scope"
     ("Type_expr.decode type_expr" (Type 30509 (Var 30509)))) |}]

let%expect_test "ambiguity-4" =
  let str =
    {|
      type 'a list =
        | Nil
        | Cons of 'a * 'a list
      ;;
      
      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;

      let (type 'a 'b) ret_f = 
        fun (eq : ('a, 'b) eq) (x : 'a) (y : 'b) ->
          match eq with
          ( Refl -> Cons (x, Cons (y, Nil))
          | _ -> Cons (x, Nil)
          )
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    ("Type escape it's equational scope"
     ("Type_expr.decode type_expr"
      (Type 30574 (Former (Constr ((Type 30597 (Var 30597))) list))))) |}]

let%expect_test "ambiguity-5" =
  let str =
    {|
      type 'a list =
        | Nil
        | Cons of 'a * 'a list
      ;;
      
      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;

      let (type 'a 'b) ret_g1 = 
        fun (eq : ('a, 'b) eq) (x : 'a) (y : 'b) ->
          match eq with
          ( Refl -> Cons (x, Cons (y, Nil))
          | _ -> Cons (y, Nil)
          )
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    ("Type escape it's equational scope"
     ("Type_expr.decode type_expr"
      (Type 30644 (Former (Constr ((Type 30667 (Var 30667))) list))))) |}]

let%expect_test "ambiguity-6" =
  let str =
    {|
      type 'a list =
        | Nil
        | Cons of 'a * 'a list
      ;;
      
      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;

      let (type 'a 'b) f = 
        fun (eq : ('a, 'b) eq) ->
          match (eq, Nil) with
          ( ( Refl, Cons ((x : 'a), Nil) ) -> Nil (* Fails bcs it cannot unify 'a = 'b outside the scope! *)
          | ( Refl, Cons ((x : 'b), Nil) ) -> Nil
          | ( _, Cons ((x : 'a), Nil) ) -> Nil
          )
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    ("Cannot unify types"
     ("Type_expr.decode type_expr1" (Type 30730 (Var 30730)))
     ("Type_expr.decode type_expr2" (Type 30752 (Var 30752)))) |}]

let%expect_test "ambiguity-6" =
  let str =
    {|
      type 'a list =
        | Nil
        | Cons of 'a * 'a list
      ;;
      
      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;

      let (type 'a 'b) g1 = 
        fun (eq : ('a, 'b) eq) ->
          match (eq, Nil) with
          ( ( Refl, Cons ((x : 'a), Nil) ) -> Nil (* Fails bcs it cannot unify 'a = 'b outside the scope! *)
          | ( Refl, Cons ((x : 'b), Nil) ) -> Nil
          | ( _, Cons ((x : 'b), Nil) ) -> Nil
          )
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    ("Cannot unify types"
     ("Type_expr.decode type_expr1" (Type 30813 (Var 30813)))
     ("Type_expr.decode type_expr2" (Type 30835 (Var 30835)))) |}]

let%expect_test "ambiguity-7" =
  let str =
    {|
      type 'a list =
        | Nil
        | Cons of 'a * 'a list
      ;;
      
      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;

      let (type 'a 'b) g2 = 
        fun (eq : ('a, 'b) eq) ->
          match (eq, Nil) with
          ( ( Refl, Cons ((x : 'b), Nil) ) -> Nil (* Fails bcs it cannot unify 'a = 'b outside the scope! *)
          | ( Refl, Cons ((x : 'a), Nil) ) -> Nil
          | ( _, Cons ((x : 'a), Nil) ) -> Nil
          )
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    ("Cannot unify types"
     ("Type_expr.decode type_expr1" (Type 30896 (Var 30896)))
     ("Type_expr.decode type_expr2" (Type 30918 (Var 30918)))) |}]

let%expect_test "ambiguity-8" =
  let str =
    {|
      type 'a list =
        | Nil
        | Cons of 'a * 'a list
      ;;
      
      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;

      let (type 'a 'b) h1 = 
        fun (eq : ('a, 'b) eq) ->
          match (eq, Nil) with
          ( ( _, Cons ((x : 'a), Nil) ) -> Nil
          | ( Refl, Cons ((x : 'a), Nil) ) -> Nil (* Fails bcs it cannot unify 'a = 'b outside the scope! *)
          | ( Refl, Cons ((x : 'b), Nil) ) -> Nil
          )
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    ("Cannot unify types"
     ("Type_expr.decode type_expr1" (Type 31002 (Var 31002)))
     ("Type_expr.decode type_expr2" (Type 31024 (Var 31024)))) |}]

let%expect_test "ambiguity-9" =
  let str =
    {|
      type 'a list =
        | Nil
        | Cons of 'a * 'a list
      ;;
      
      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;

      let (type 'a 'b) h2 = 
        fun (eq : ('a, 'b) eq) ->
          match (eq, Nil) with
          ( ( _, Cons ((x : 'b), Nil) ) -> Nil
          | ( Refl, Cons ((x : 'a), Nil) ) -> Nil (* Fails bcs it cannot unify 'a = 'b outside the scope! *)
          | ( Refl, Cons ((x : 'b), Nil) ) -> Nil
          )
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    ("Cannot unify types"
     ("Type_expr.decode type_expr1" (Type 31081 (Var 31081)))
     ("Type_expr.decode type_expr2" (Type 31103 (Var 31103)))) |}]

let%expect_test "ambiguity-10" =
  let str =
    {|
      type 'a list =
        | Nil
        | Cons of 'a * 'a list
      ;;
      
      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;

      let (type 'a 'b) h3 = 
        fun (eq : ('a, 'b) eq) ->
          match (eq, Nil) with
          ( ( _, Cons ((x : 'a), Nil) ) -> Nil
          | ( Refl, Cons ((x : 'b), Nil) ) -> Nil (* Fails bcs it cannot unify 'a = 'b outside the scope! *)
          | ( Refl, Cons ((x : 'a), Nil) ) -> Nil
          )
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    ("Cannot unify types"
     ("Type_expr.decode type_expr1" (Type 31160 (Var 31160)))
     ("Type_expr.decode type_expr2" (Type 31182 (Var 31182)))) |}]
