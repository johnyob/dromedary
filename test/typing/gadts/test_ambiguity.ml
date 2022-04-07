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
    ("Type escape it's equational scope" (type_expr ((desc (Ttyp_var a92))))) |}]

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
    ("Type escape it's equational scope" (type_expr ((desc (Ttyp_var a94))))) |}]

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
    ("Type escape it's equational scope" (type_expr ((desc (Ttyp_var a96))))) |}]

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
     (type_expr ((desc (Ttyp_constr ((((desc (Ttyp_var a97)))) list)))))) |}]

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
     (type_expr ((desc (Ttyp_constr ((((desc (Ttyp_var a99)))) list)))))) |}]

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
    ("Cannot unify types" (type_expr1 ((desc (Ttyp_var a101))))
     (type_expr2 ((desc (Ttyp_var a102))))) |}]

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
    ("Cannot unify types" (type_expr1 ((desc (Ttyp_var a103))))
     (type_expr2 ((desc (Ttyp_var a104))))) |}]

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
    ("Cannot unify types" (type_expr1 ((desc (Ttyp_var a106))))
     (type_expr2 ((desc (Ttyp_var a105))))) |}]

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
    ("Cannot unify types" (type_expr1 ((desc (Ttyp_var a107))))
     (type_expr2 ((desc (Ttyp_var a108))))) |}]

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
    ("Cannot unify types" (type_expr1 ((desc (Ttyp_var a110))))
     (type_expr2 ((desc (Ttyp_var a109))))) |}]

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
    ("Cannot unify types" (type_expr1 ((desc (Ttyp_var a111))))
     (type_expr2 ((desc (Ttyp_var a112))))) |}]
