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
     ("Type_expr.decode type_expr" (Type 28 (Var 28)))) |}]


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
     ("Type_expr.decode type_expr" (Type 28 (Var 28)))) |}]


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
     ("Type_expr.decode type_expr" (Type 24 (Var 24)))) |}]


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
      (Type 36 (Former (Constr ((Type 59 (Var 59))) list))))) |}]


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
      (Type 36 (Former (Constr ((Type 59 (Var 59))) list))))) |}]


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
    ("Cannot unify types" ("Type_expr.decode type_expr1" (Type 52 (Var 52)))
     ("Type_expr.decode type_expr2" (Type 74 (Var 74)))) |}]


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
    ("Cannot unify types" ("Type_expr.decode type_expr1" (Type 52 (Var 52)))
     ("Type_expr.decode type_expr2" (Type 74 (Var 74)))) |}]


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
    ("Cannot unify types" ("Type_expr.decode type_expr1" (Type 52 (Var 52)))
     ("Type_expr.decode type_expr2" (Type 74 (Var 74)))) |}]


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
    ("Cannot unify types" ("Type_expr.decode type_expr1" (Type 75 (Var 75)))
     ("Type_expr.decode type_expr2" (Type 97 (Var 97)))) |}]


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
    ("Cannot unify types" ("Type_expr.decode type_expr1" (Type 48 (Var 48)))
     ("Type_expr.decode type_expr2" (Type 70 (Var 70)))) |}]


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
    ("Cannot unify types" ("Type_expr.decode type_expr1" (Type 48 (Var 48)))
     ("Type_expr.decode type_expr2" (Type 70 (Var 70)))) |}]
