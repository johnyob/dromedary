open! Import
open Util

(* Tests from typing-gadts/dynamic_frisch.ml
   -------------------------------------------
   24/24
*)

let%expect_test "dynamic-frisch" =
  let str =
    {|
      type 'a list = 
        | Nil 
        | Cons of 'a * 'a list
      ;;

      external raise : 'a. exn -> 'a = "%raise";;
      external map : 'a 'b. 'a list -> ('a -> 'b) -> 'b list = "%map";; 
      external hole : 'a. 'a = "%hole";;
      external length : 'a. 'a list -> int = "%length";;
      external not_eq : 'a. 'a -> 'a -> bool = "%not_equal";;
      external iter2 : 'a 'b. 'a list -> 'b list -> ('a -> 'b -> unit) -> unit = "%iter2";;

      type 'a ty = 
        | Int constraint 'a = int
        | String constraint 'a = string
        | List of 'b. 'b ty constraint 'a = 'b list
        | Pair of 'b 'c. 'b ty * 'c ty constraint 'a = 'b * 'c
        | Record of 'builder. ('a, 'builder) record

      and ('a, 'builder) record = 
        { path: string
        ; fields : ('a, 'builder) packed_field list
        ; create_builder : unit -> 'builder
        ; of_builder : 'builder -> 'a 
        }

      and ('a, 'builder) packed_field = 
        | Field of 'b. ('a, 'builder, 'b) field

      and ('a, 'builder, 'b) field = 
        { label: string
        ; type_ : 'b ty
        ; get : 'a -> 'b
        ; set : 'builder -> 'b -> unit
        }
      ;;

      type variant = 
        | Var_int of int
        | Var_string of string
        | Var_list of variant list
        | Var_pair of variant * variant
        | Var_record of (string * variant) list
      ;;

      external hole : 'a. 'a = "%hole";;

      let rec (type 't) variantize = 
        fun (ty : 't ty) (x : 't) ->
          (match ty with
           ( Int -> Var_int x
           | String -> Var_string x
           | List ty -> Var_list (map x (variantize ty))
           | Pair (ty1, ty2) ->
              let (x1, x2) = x in
              Var_pair (variantize ty1 x1, variantize ty2 x2)
           | Record record ->
              let f = fun (Field field) ->
                (field.label, variantize field.type_ (field.get x))
              in
              Var_record (map record.fields f)
           )
          : variant)
      ;; 

      exception Variant_mismatch;;

      let rec (type 't) devariantize = 
        fun (ty : 't ty) (v : variant) ->
          (match (ty, v) with
           ( (Int, Var_int x) -> x
           | (String, Var_string x) -> x
           | (List ty, Var_list vs) -> map vs (devariantize ty)
           | (Pair (ty1, ty2), Var_pair (v1, v2)) ->
              (devariantize ty1 v1, devariantize ty2 v2)
          | (Record record, Var_record vfields) ->
            (if not_eq (length record.fields) (length vfields) then raise Variant_mismatch else ());
             let builder = record.create_builder () in
             let f = fun (Field field) (label, v) ->
              (if not_eq (field.label) label then raise Variant_mismatch else ());
              field.set builder (devariantize field.type_ v) 
             in
             iter2 record.fields vfields f;
             record.of_builder builder
           | _ -> raise Variant_mismatch
           ) 
          : 't)
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: list
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: 45
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 45
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 45
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 45
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: 45
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 45
       └──Structure item: Primitive
          └──Value description:
             └──Name: raise
             └──Scheme:
                └──Variables: 0
                └──Type expr: Arrow
                   └──Type expr: Constructor: exn
                   └──Type expr: Variable: 0
             └──Primitive name: %raise
       └──Structure item: Primitive
          └──Value description:
             └──Name: map
             └──Scheme:
                └──Variables: 6,5
                └──Type expr: Arrow
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: 5
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: 5
                         └──Type expr: Variable: 6
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 6
             └──Primitive name: %map
       └──Structure item: Primitive
          └──Value description:
             └──Name: hole
             └──Scheme:
                └──Variables: 17
                └──Type expr: Variable: 17
             └──Primitive name: %hole
       └──Structure item: Primitive
          └──Value description:
             └──Name: length
             └──Scheme:
                └──Variables: 18
                └──Type expr: Arrow
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: 18
                   └──Type expr: Constructor: int
             └──Primitive name: %length
       └──Structure item: Primitive
          └──Value description:
             └──Name: not_eq
             └──Scheme:
                └──Variables: 25
                └──Type expr: Arrow
                   └──Type expr: Variable: 25
                   └──Type expr: Arrow
                      └──Type expr: Variable: 25
                      └──Type expr: Constructor: bool
             └──Primitive name: %not_equal
       └──Structure item: Primitive
          └──Value description:
             └──Name: iter2
             └──Scheme:
                └──Variables: 33,32
                └──Type expr: Arrow
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: 32
                   └──Type expr: Arrow
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 33
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: 32
                            └──Type expr: Arrow
                               └──Type expr: Variable: 33
                               └──Type expr: Constructor: unit
                         └──Type expr: Constructor: unit
             └──Primitive name: %iter2
       └──Structure item: Type
          └──Type declaration:
             └──Type name: ty
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Int
                   └──Constructor alphas: 50
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 50
                   └──Constraint:
                      └──Type expr: Variable: 50
                      └──Type expr: Constructor: int
                └──Constructor declaration:
                   └──Constructor name: String
                   └──Constructor alphas: 50
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 50
                   └──Constraint:
                      └──Type expr: Variable: 50
                      └──Type expr: Constructor: string
                └──Constructor declaration:
                   └──Constructor name: List
                   └──Constructor alphas: 50
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 50
                   └──Constructor argument:
                      └──Constructor betas: 55
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 55
                   └──Constraint:
                      └──Type expr: Variable: 50
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 55
                └──Constructor declaration:
                   └──Constructor name: Pair
                   └──Constructor alphas: 50
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 50
                   └──Constructor argument:
                      └──Constructor betas: 60 59
                      └──Type expr: Tuple
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 59
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 60
                   └──Constraint:
                      └──Type expr: Variable: 50
                      └──Type expr: Tuple
                         └──Type expr: Variable: 59
                         └──Type expr: Variable: 60
                └──Constructor declaration:
                   └──Constructor name: Record
                   └──Constructor alphas: 50
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 50
                   └──Constructor argument:
                      └──Constructor betas: 66
                      └──Type expr: Constructor: record
                         └──Type expr: Variable: 50
                         └──Type expr: Variable: 66
          └──Type declaration:
             └──Type name: record
             └──Type declaration kind: Record
                └──Label declaration:
                   └──Label name: path
                   └──Label alphas: 69 70
                   └──Label betas:
                   └──Type expr: Constructor: string
                   └──Type expr: Constructor: record
                      └──Type expr: Variable: 69
                      └──Type expr: Variable: 70
                └──Label declaration:
                   └──Label name: fields
                   └──Label alphas: 69 70
                   └──Label betas:
                   └──Type expr: Constructor: list
                      └──Type expr: Constructor: packed_field
                         └──Type expr: Variable: 69
                         └──Type expr: Variable: 70
                   └──Type expr: Constructor: record
                      └──Type expr: Variable: 69
                      └──Type expr: Variable: 70
                └──Label declaration:
                   └──Label name: create_builder
                   └──Label alphas: 69 70
                   └──Label betas:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: unit
                      └──Type expr: Variable: 70
                   └──Type expr: Constructor: record
                      └──Type expr: Variable: 69
                      └──Type expr: Variable: 70
                └──Label declaration:
                   └──Label name: of_builder
                   └──Label alphas: 69 70
                   └──Label betas:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 70
                      └──Type expr: Variable: 69
                   └──Type expr: Constructor: record
                      └──Type expr: Variable: 69
                      └──Type expr: Variable: 70
          └──Type declaration:
             └──Type name: packed_field
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Field
                   └──Constructor alphas: 81 82
                   └──Constructor type:
                      └──Type expr: Constructor: packed_field
                         └──Type expr: Variable: 81
                         └──Type expr: Variable: 82
                   └──Constructor argument:
                      └──Constructor betas: 83
                      └──Type expr: Constructor: field
                         └──Type expr: Variable: 81
                         └──Type expr: Variable: 82
                         └──Type expr: Variable: 83
          └──Type declaration:
             └──Type name: field
             └──Type declaration kind: Record
                └──Label declaration:
                   └──Label name: label
                   └──Label alphas: 86 87 88
                   └──Label betas:
                   └──Type expr: Constructor: string
                   └──Type expr: Constructor: field
                      └──Type expr: Variable: 86
                      └──Type expr: Variable: 87
                      └──Type expr: Variable: 88
                └──Label declaration:
                   └──Label name: type_
                   └──Label alphas: 86 87 88
                   └──Label betas:
                   └──Type expr: Constructor: ty
                      └──Type expr: Variable: 88
                   └──Type expr: Constructor: field
                      └──Type expr: Variable: 86
                      └──Type expr: Variable: 87
                      └──Type expr: Variable: 88
                └──Label declaration:
                   └──Label name: get
                   └──Label alphas: 86 87 88
                   └──Label betas:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 86
                      └──Type expr: Variable: 88
                   └──Type expr: Constructor: field
                      └──Type expr: Variable: 86
                      └──Type expr: Variable: 87
                      └──Type expr: Variable: 88
                └──Label declaration:
                   └──Label name: set
                   └──Label alphas: 86 87 88
                   └──Label betas:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 87
                      └──Type expr: Arrow
                         └──Type expr: Variable: 88
                         └──Type expr: Constructor: unit
                   └──Type expr: Constructor: field
                      └──Type expr: Variable: 86
                      └──Type expr: Variable: 87
                      └──Type expr: Variable: 88
       └──Structure item: Type
          └──Type declaration:
             └──Type name: variant
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Var_int
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: variant
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: int
                └──Constructor declaration:
                   └──Constructor name: Var_string
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: variant
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: string
                └──Constructor declaration:
                   └──Constructor name: Var_list
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: variant
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: list
                         └──Type expr: Constructor: variant
                └──Constructor declaration:
                   └──Constructor name: Var_pair
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: variant
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Constructor: variant
                         └──Type expr: Constructor: variant
                └──Constructor declaration:
                   └──Constructor name: Var_record
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: variant
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: list
                         └──Type expr: Tuple
                            └──Type expr: Constructor: string
                            └──Type expr: Constructor: variant
       └──Structure item: Primitive
          └──Value description:
             └──Name: hole
             └──Scheme:
                └──Variables: 52
                └──Type expr: Variable: 52
             └──Primitive name: %hole
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: variantize
                └──Abstraction:
                   └──Variables: 61
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 82
                         └──Type expr: Arrow
                            └──Type expr: Variable: 82
                            └──Type expr: Constructor: variant
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: 82
                            └──Desc: Variable: ty
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: 82
                               └──Type expr: Constructor: variant
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: 82
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Constructor: variant
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: ty
                                           └──Type expr: Variable: 82
                                        └──Desc: Variable
                                           └──Variable: ty
                                     └──Type expr: Constructor: ty
                                        └──Type expr: Variable: 82
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: ty
                                                 └──Type expr: Variable: 82
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Int
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: 82
                                           └──Expression:
                                              └──Type expr: Constructor: variant
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Var_int
                                                    └──Constructor argument type:
                                                       └──Type expr: Variable: 82
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: variant
                                                 └──Expression:
                                                    └──Type expr: Variable: 82
                                                    └──Desc: Variable
                                                       └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: ty
                                                 └──Type expr: Variable: 82
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: String
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: 82
                                           └──Expression:
                                              └──Type expr: Constructor: variant
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Var_string
                                                    └──Constructor argument type:
                                                       └──Type expr: Variable: 82
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: variant
                                                 └──Expression:
                                                    └──Type expr: Variable: 82
                                                    └──Desc: Variable
                                                       └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: ty
                                                 └──Type expr: Variable: 82
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: List
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: 128
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: 82
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 128
                                                    └──Desc: Variable: ty
                                           └──Expression:
                                              └──Type expr: Constructor: variant
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Var_list
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Constructor: variant
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: variant
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: variant
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: 128
                                                                └──Type expr: Constructor: variant
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: variant
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: 82
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: 128
                                                                         └──Type expr: Constructor: variant
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: variant
                                                                └──Desc: Variable
                                                                   └──Variable: map
                                                                   └──Type expr: Constructor: variant
                                                                   └──Type expr: Variable: 128
                                                             └──Expression:
                                                                └──Type expr: Variable: 82
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: 128
                                                             └──Type expr: Constructor: variant
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: 128
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: 128
                                                                      └──Type expr: Constructor: variant
                                                                └──Desc: Variable
                                                                   └──Variable: variantize
                                                                   └──Type expr: Variable: 128
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 128
                                                                └──Desc: Variable
                                                                   └──Variable: ty
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: ty
                                                 └──Type expr: Variable: 82
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Pair
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: 179
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: 177
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: 82
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: 179
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: 177
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: 179
                                                          └──Desc: Variable: ty1
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: 177
                                                          └──Desc: Variable: ty2
                                           └──Expression:
                                              └──Type expr: Constructor: variant
                                              └──Desc: Let
                                                 └──Value bindings:
                                                    └──Value binding:
                                                       └──Pattern:
                                                          └──Type expr: Variable: 82
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Variable: 179
                                                                └──Desc: Variable: x1
                                                             └──Pattern:
                                                                └──Type expr: Variable: 177
                                                                └──Desc: Variable: x2
                                                       └──Abstraction:
                                                          └──Variables:
                                                          └──Expression:
                                                             └──Type expr: Variable: 82
                                                             └──Desc: Variable
                                                                └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: variant
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Var_pair
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: variant
                                                                └──Type expr: Constructor: variant
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: variant
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: variant
                                                             └──Type expr: Constructor: variant
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Constructor: variant
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: 179
                                                                         └──Type expr: Constructor: variant
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: ty
                                                                                  └──Type expr: Variable: 179
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Variable: 179
                                                                                  └──Type expr: Constructor: variant
                                                                            └──Desc: Variable
                                                                               └──Variable: variantize
                                                                               └──Type expr: Variable: 179
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: 179
                                                                            └──Desc: Variable
                                                                               └──Variable: ty1
                                                                   └──Expression:
                                                                      └──Type expr: Variable: 179
                                                                      └──Desc: Variable
                                                                         └──Variable: x1
                                                             └──Expression:
                                                                └──Type expr: Constructor: variant
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: 177
                                                                         └──Type expr: Constructor: variant
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: ty
                                                                                  └──Type expr: Variable: 177
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Variable: 177
                                                                                  └──Type expr: Constructor: variant
                                                                            └──Desc: Variable
                                                                               └──Variable: variantize
                                                                               └──Type expr: Variable: 177
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: 177
                                                                            └──Desc: Variable
                                                                               └──Variable: ty2
                                                                   └──Expression:
                                                                      └──Type expr: Variable: 177
                                                                      └──Desc: Variable
                                                                         └──Variable: x2
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: ty
                                                 └──Type expr: Variable: 82
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Record
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: record
                                                          └──Type expr: Variable: 82
                                                          └──Type expr: Variable: 243
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: 82
                                                 └──Pattern:
                                                    └──Type expr: Constructor: record
                                                       └──Type expr: Variable: 82
                                                       └──Type expr: Variable: 243
                                                    └──Desc: Variable: record
                                           └──Expression:
                                              └──Type expr: Constructor: variant
                                              └──Desc: Let
                                                 └──Value bindings:
                                                    └──Value binding:
                                                       └──Pattern:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: packed_field
                                                                └──Type expr: Variable: 82
                                                                └──Type expr: Variable: 256
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: string
                                                                └──Type expr: Constructor: variant
                                                          └──Desc: Variable: f
                                                       └──Abstraction:
                                                          └──Variables: 256,256,256,256
                                                          └──Expression:
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: packed_field
                                                                   └──Type expr: Variable: 82
                                                                   └──Type expr: Variable: 256
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: string
                                                                   └──Type expr: Constructor: variant
                                                             └──Desc: Function
                                                                └──Pattern:
                                                                   └──Type expr: Constructor: packed_field
                                                                      └──Type expr: Variable: 82
                                                                      └──Type expr: Variable: 256
                                                                   └──Desc: Construct
                                                                      └──Constructor description:
                                                                         └──Name: Field
                                                                         └──Constructor argument type:
                                                                            └──Type expr: Constructor: field
                                                                               └──Type expr: Variable: 82
                                                                               └──Type expr: Variable: 256
                                                                               └──Type expr: Variable: 259
                                                                         └──Constructor type:
                                                                            └──Type expr: Constructor: packed_field
                                                                               └──Type expr: Variable: 82
                                                                               └──Type expr: Variable: 256
                                                                      └──Pattern:
                                                                         └──Type expr: Constructor: field
                                                                            └──Type expr: Variable: 82
                                                                            └──Type expr: Variable: 256
                                                                            └──Type expr: Variable: 259
                                                                         └──Desc: Variable: field
                                                                └──Expression:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: string
                                                                      └──Type expr: Constructor: variant
                                                                   └──Desc: Tuple
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: string
                                                                         └──Desc: Field
                                                                            └──Expression:
                                                                               └──Type expr: Constructor: field
                                                                                  └──Type expr: Variable: 82
                                                                                  └──Type expr: Variable: 256
                                                                                  └──Type expr: Variable: 259
                                                                               └──Desc: Variable
                                                                                  └──Variable: field
                                                                            └──Label description:
                                                                               └──Label: label
                                                                               └──Label argument type:
                                                                                  └──Type expr: Constructor: string
                                                                               └──Label type:
                                                                                  └──Type expr: Constructor: field
                                                                                     └──Type expr: Variable: 82
                                                                                     └──Type expr: Variable: 256
                                                                                     └──Type expr: Variable: 259
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: variant
                                                                         └──Desc: Application
                                                                            └──Expression:
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Variable: 259
                                                                                  └──Type expr: Constructor: variant
                                                                               └──Desc: Application
                                                                                  └──Expression:
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Constructor: ty
                                                                                           └──Type expr: Variable: 259
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Variable: 259
                                                                                           └──Type expr: Constructor: variant
                                                                                     └──Desc: Variable
                                                                                        └──Variable: variantize
                                                                                        └──Type expr: Variable: 259
                                                                                  └──Expression:
                                                                                     └──Type expr: Constructor: ty
                                                                                        └──Type expr: Variable: 259
                                                                                     └──Desc: Field
                                                                                        └──Expression:
                                                                                           └──Type expr: Constructor: field
                                                                                              └──Type expr: Variable: 82
                                                                                              └──Type expr: Variable: 256
                                                                                              └──Type expr: Variable: 259
                                                                                           └──Desc: Variable
                                                                                              └──Variable: field
                                                                                        └──Label description:
                                                                                           └──Label: type_
                                                                                           └──Label argument type:
                                                                                              └──Type expr: Constructor: ty
                                                                                                 └──Type expr: Variable: 259
                                                                                           └──Label type:
                                                                                              └──Type expr: Constructor: field
                                                                                                 └──Type expr: Variable: 82
                                                                                                 └──Type expr: Variable: 256
                                                                                                 └──Type expr: Variable: 259
                                                                            └──Expression:
                                                                               └──Type expr: Variable: 259
                                                                               └──Desc: Application
                                                                                  └──Expression:
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Variable: 82
                                                                                        └──Type expr: Variable: 259
                                                                                     └──Desc: Field
                                                                                        └──Expression:
                                                                                           └──Type expr: Constructor: field
                                                                                              └──Type expr: Variable: 82
                                                                                              └──Type expr: Variable: 256
                                                                                              └──Type expr: Variable: 259
                                                                                           └──Desc: Variable
                                                                                              └──Variable: field
                                                                                        └──Label description:
                                                                                           └──Label: get
                                                                                           └──Label argument type:
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Variable: 82
                                                                                                 └──Type expr: Variable: 259
                                                                                           └──Label type:
                                                                                              └──Type expr: Constructor: field
                                                                                                 └──Type expr: Variable: 82
                                                                                                 └──Type expr: Variable: 256
                                                                                                 └──Type expr: Variable: 259
                                                                                  └──Expression:
                                                                                     └──Type expr: Variable: 82
                                                                                     └──Desc: Variable
                                                                                        └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: variant
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Var_record
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: string
                                                                   └──Type expr: Constructor: variant
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: variant
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: string
                                                                └──Type expr: Constructor: variant
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: packed_field
                                                                         └──Type expr: Variable: 82
                                                                         └──Type expr: Variable: 243
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Constructor: string
                                                                         └──Type expr: Constructor: variant
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Constructor: string
                                                                         └──Type expr: Constructor: variant
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Constructor: packed_field
                                                                               └──Type expr: Variable: 82
                                                                               └──Type expr: Variable: 243
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: packed_field
                                                                                  └──Type expr: Variable: 82
                                                                                  └──Type expr: Variable: 243
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Constructor: string
                                                                                  └──Type expr: Constructor: variant
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Constructor: string
                                                                                  └──Type expr: Constructor: variant
                                                                      └──Desc: Variable
                                                                         └──Variable: map
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Constructor: string
                                                                            └──Type expr: Constructor: variant
                                                                         └──Type expr: Constructor: packed_field
                                                                            └──Type expr: Variable: 82
                                                                            └──Type expr: Variable: 243
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: packed_field
                                                                            └──Type expr: Variable: 82
                                                                            └──Type expr: Variable: 243
                                                                      └──Desc: Field
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: record
                                                                               └──Type expr: Variable: 82
                                                                               └──Type expr: Variable: 243
                                                                            └──Desc: Variable
                                                                               └──Variable: record
                                                                         └──Label description:
                                                                            └──Label: fields
                                                                            └──Label argument type:
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Constructor: packed_field
                                                                                     └──Type expr: Variable: 82
                                                                                     └──Type expr: Variable: 243
                                                                            └──Label type:
                                                                               └──Type expr: Constructor: record
                                                                                  └──Type expr: Variable: 82
                                                                                  └──Type expr: Variable: 243
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: packed_field
                                                                      └──Type expr: Variable: 82
                                                                      └──Type expr: Variable: 243
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: string
                                                                      └──Type expr: Constructor: variant
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                                   └──Type expr: Variable: 243
       └──Structure item: Exception
          └──Type exception:
             └──Extension constructor:
                └──Extension name: exn
                └──Extension parameters:
                └──Extension constructor kind: Declaration
                   └──Constructor declaration:
                      └──Constructor name: Variant_mismatch
                      └──Constructor alphas:
                      └──Constructor type:
                         └──Type expr: Constructor: exn
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: devariantize
                └──Abstraction:
                   └──Variables: 363
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 384
                         └──Type expr: Arrow
                            └──Type expr: Constructor: variant
                            └──Type expr: Variable: 384
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: 384
                            └──Desc: Variable: ty
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: variant
                               └──Type expr: Variable: 384
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: variant
                                  └──Desc: Variable: v
                               └──Expression:
                                  └──Type expr: Variable: 384
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: ty
                                              └──Type expr: Variable: 384
                                           └──Type expr: Constructor: variant
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: ty
                                                 └──Type expr: Variable: 384
                                              └──Desc: Variable
                                                 └──Variable: ty
                                           └──Expression:
                                              └──Type expr: Constructor: variant
                                              └──Desc: Variable
                                                 └──Variable: v
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: ty
                                           └──Type expr: Variable: 384
                                        └──Type expr: Constructor: variant
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 384
                                                 └──Type expr: Constructor: variant
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 384
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 384
                                                 └──Pattern:
                                                    └──Type expr: Constructor: variant
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Var_int
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: variant
                                                       └──Pattern:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Variable: 384
                                              └──Desc: Variable
                                                 └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 384
                                                 └──Type expr: Constructor: variant
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 384
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: String
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 384
                                                 └──Pattern:
                                                    └──Type expr: Constructor: variant
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Var_string
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: string
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: variant
                                                       └──Pattern:
                                                          └──Type expr: Constructor: string
                                                          └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Variable: 384
                                              └──Desc: Variable
                                                 └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 384
                                                 └──Type expr: Constructor: variant
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 384
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: List
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 450
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 384
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: 450
                                                          └──Desc: Variable: ty
                                                 └──Pattern:
                                                    └──Type expr: Constructor: variant
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Var_list
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: variant
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: variant
                                                       └──Pattern:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: variant
                                                          └──Desc: Variable: vs
                                           └──Expression:
                                              └──Type expr: Variable: 384
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: variant
                                                          └──Type expr: Variable: 450
                                                       └──Type expr: Variable: 384
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: variant
                                                             └──Type expr: Arrow
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: variant
                                                                   └──Type expr: Variable: 450
                                                                └──Type expr: Variable: 384
                                                          └──Desc: Variable
                                                             └──Variable: map
                                                             └──Type expr: Variable: 450
                                                             └──Type expr: Constructor: variant
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: variant
                                                          └──Desc: Variable
                                                             └──Variable: vs
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: variant
                                                       └──Type expr: Variable: 450
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 450
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: variant
                                                                └──Type expr: Variable: 450
                                                          └──Desc: Variable
                                                             └──Variable: devariantize
                                                             └──Type expr: Variable: 450
                                                       └──Expression:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: 450
                                                          └──Desc: Variable
                                                             └──Variable: ty
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 384
                                                 └──Type expr: Constructor: variant
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 384
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Pair
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 510
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 508
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 384
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 510
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 508
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 510
                                                                └──Desc: Variable: ty1
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 508
                                                                └──Desc: Variable: ty2
                                                 └──Pattern:
                                                    └──Type expr: Constructor: variant
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Var_pair
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: variant
                                                                └──Type expr: Constructor: variant
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: variant
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: variant
                                                             └──Type expr: Constructor: variant
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: variant
                                                                └──Desc: Variable: v1
                                                             └──Pattern:
                                                                └──Type expr: Constructor: variant
                                                                └──Desc: Variable: v2
                                           └──Expression:
                                              └──Type expr: Variable: 384
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Variable: 510
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: variant
                                                             └──Type expr: Variable: 510
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: 510
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: variant
                                                                      └──Type expr: Variable: 510
                                                                └──Desc: Variable
                                                                   └──Variable: devariantize
                                                                   └──Type expr: Variable: 510
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 510
                                                                └──Desc: Variable
                                                                   └──Variable: ty1
                                                       └──Expression:
                                                          └──Type expr: Constructor: variant
                                                          └──Desc: Variable
                                                             └──Variable: v1
                                                 └──Expression:
                                                    └──Type expr: Variable: 508
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: variant
                                                             └──Type expr: Variable: 508
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: 508
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: variant
                                                                      └──Type expr: Variable: 508
                                                                └──Desc: Variable
                                                                   └──Variable: devariantize
                                                                   └──Type expr: Variable: 508
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 508
                                                                └──Desc: Variable
                                                                   └──Variable: ty2
                                                       └──Expression:
                                                          └──Type expr: Constructor: variant
                                                          └──Desc: Variable
                                                             └──Variable: v2
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 384
                                                 └──Type expr: Constructor: variant
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 384
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Record
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: record
                                                                └──Type expr: Variable: 384
                                                                └──Type expr: Variable: 576
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 384
                                                       └──Pattern:
                                                          └──Type expr: Constructor: record
                                                             └──Type expr: Variable: 384
                                                             └──Type expr: Variable: 576
                                                          └──Desc: Variable: record
                                                 └──Pattern:
                                                    └──Type expr: Constructor: variant
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Var_record
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: string
                                                                   └──Type expr: Constructor: variant
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: variant
                                                       └──Pattern:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: string
                                                                └──Type expr: Constructor: variant
                                                          └──Desc: Variable: vfields
                                           └──Expression:
                                              └──Type expr: Variable: 384
                                              └──Desc: Sequence
                                                 └──Expression:
                                                    └──Type expr: Constructor: unit
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
                                                                      └──Desc: Variable
                                                                         └──Variable: not_eq
                                                                         └──Type expr: Constructor: int
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: int
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Constructor: packed_field
                                                                                     └──Type expr: Variable: 384
                                                                                     └──Type expr: Variable: 576
                                                                               └──Type expr: Constructor: int
                                                                            └──Desc: Variable
                                                                               └──Variable: length
                                                                               └──Type expr: Constructor: packed_field
                                                                                  └──Type expr: Variable: 384
                                                                                  └──Type expr: Variable: 576
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: packed_field
                                                                                  └──Type expr: Variable: 384
                                                                                  └──Type expr: Variable: 576
                                                                            └──Desc: Field
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: record
                                                                                     └──Type expr: Variable: 384
                                                                                     └──Type expr: Variable: 576
                                                                                  └──Desc: Variable
                                                                                     └──Variable: record
                                                                               └──Label description:
                                                                                  └──Label: fields
                                                                                  └──Label argument type:
                                                                                     └──Type expr: Constructor: list
                                                                                        └──Type expr: Constructor: packed_field
                                                                                           └──Type expr: Variable: 384
                                                                                           └──Type expr: Variable: 576
                                                                                  └──Label type:
                                                                                     └──Type expr: Constructor: record
                                                                                        └──Type expr: Variable: 384
                                                                                        └──Type expr: Variable: 576
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Constructor: string
                                                                               └──Type expr: Constructor: variant
                                                                         └──Type expr: Constructor: int
                                                                      └──Desc: Variable
                                                                         └──Variable: length
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Constructor: string
                                                                            └──Type expr: Constructor: variant
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Constructor: string
                                                                            └──Type expr: Constructor: variant
                                                                      └──Desc: Variable
                                                                         └──Variable: vfields
                                                       └──Expression:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: exn
                                                                   └──Type expr: Constructor: unit
                                                                └──Desc: Variable
                                                                   └──Variable: raise
                                                                   └──Type expr: Constructor: unit
                                                             └──Expression:
                                                                └──Type expr: Constructor: exn
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Variant_mismatch
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: exn
                                                       └──Expression:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                                 └──Expression:
                                                    └──Type expr: Variable: 384
                                                    └──Desc: Let
                                                       └──Value bindings:
                                                          └──Value binding:
                                                             └──Pattern:
                                                                └──Type expr: Variable: 576
                                                                └──Desc: Variable: builder
                                                             └──Abstraction:
                                                                └──Variables:
                                                                └──Expression:
                                                                   └──Type expr: Variable: 576
                                                                   └──Desc: Application
                                                                      └──Expression:
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: 576
                                                                         └──Desc: Field
                                                                            └──Expression:
                                                                               └──Type expr: Constructor: record
                                                                                  └──Type expr: Variable: 384
                                                                                  └──Type expr: Variable: 576
                                                                               └──Desc: Variable
                                                                                  └──Variable: record
                                                                            └──Label description:
                                                                               └──Label: create_builder
                                                                               └──Label argument type:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: unit
                                                                                     └──Type expr: Variable: 576
                                                                               └──Label type:
                                                                                  └──Type expr: Constructor: record
                                                                                     └──Type expr: Variable: 384
                                                                                     └──Type expr: Variable: 576
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: unit
                                                                         └──Desc: Constant: ()
                                                       └──Expression:
                                                          └──Type expr: Variable: 384
                                                          └──Desc: Let
                                                             └──Value bindings:
                                                                └──Value binding:
                                                                   └──Pattern:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: packed_field
                                                                            └──Type expr: Variable: 658
                                                                            └──Type expr: Variable: 576
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Constructor: string
                                                                               └──Type expr: Constructor: variant
                                                                            └──Type expr: Constructor: unit
                                                                      └──Desc: Variable: f
                                                                   └──Abstraction:
                                                                      └──Variables: 658,658,658,658
                                                                      └──Expression:
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: packed_field
                                                                               └──Type expr: Variable: 658
                                                                               └──Type expr: Variable: 576
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Constructor: string
                                                                                  └──Type expr: Constructor: variant
                                                                               └──Type expr: Constructor: unit
                                                                         └──Desc: Function
                                                                            └──Pattern:
                                                                               └──Type expr: Constructor: packed_field
                                                                                  └──Type expr: Variable: 658
                                                                                  └──Type expr: Variable: 576
                                                                               └──Desc: Construct
                                                                                  └──Constructor description:
                                                                                     └──Name: Field
                                                                                     └──Constructor argument type:
                                                                                        └──Type expr: Constructor: field
                                                                                           └──Type expr: Variable: 658
                                                                                           └──Type expr: Variable: 576
                                                                                           └──Type expr: Variable: 662
                                                                                     └──Constructor type:
                                                                                        └──Type expr: Constructor: packed_field
                                                                                           └──Type expr: Variable: 658
                                                                                           └──Type expr: Variable: 576
                                                                                  └──Pattern:
                                                                                     └──Type expr: Constructor: field
                                                                                        └──Type expr: Variable: 658
                                                                                        └──Type expr: Variable: 576
                                                                                        └──Type expr: Variable: 662
                                                                                     └──Desc: Variable: field
                                                                            └──Expression:
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Constructor: string
                                                                                     └──Type expr: Constructor: variant
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Desc: Function
                                                                                  └──Pattern:
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Constructor: string
                                                                                        └──Type expr: Constructor: variant
                                                                                     └──Desc: Tuple
                                                                                        └──Pattern:
                                                                                           └──Type expr: Constructor: string
                                                                                           └──Desc: Variable: label
                                                                                        └──Pattern:
                                                                                           └──Type expr: Constructor: variant
                                                                                           └──Desc: Variable: v
                                                                                  └──Expression:
                                                                                     └──Type expr: Constructor: unit
                                                                                     └──Desc: Sequence
                                                                                        └──Expression:
                                                                                           └──Type expr: Constructor: unit
                                                                                           └──Desc: If
                                                                                              └──Expression:
                                                                                                 └──Type expr: Constructor: bool
                                                                                                 └──Desc: Application
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Constructor: string
                                                                                                          └──Type expr: Constructor: bool
                                                                                                       └──Desc: Application
                                                                                                          └──Expression:
                                                                                                             └──Type expr: Arrow
                                                                                                                └──Type expr: Constructor: string
                                                                                                                └──Type expr: Arrow
                                                                                                                   └──Type expr: Constructor: string
                                                                                                                   └──Type expr: Constructor: bool
                                                                                                             └──Desc: Variable
                                                                                                                └──Variable: not_eq
                                                                                                                └──Type expr: Constructor: string
                                                                                                          └──Expression:
                                                                                                             └──Type expr: Constructor: string
                                                                                                             └──Desc: Field
                                                                                                                └──Expression:
                                                                                                                   └──Type expr: Constructor: field
                                                                                                                      └──Type expr: Variable: 658
                                                                                                                      └──Type expr: Variable: 576
                                                                                                                      └──Type expr: Variable: 662
                                                                                                                   └──Desc: Variable
                                                                                                                      └──Variable: field
                                                                                                                └──Label description:
                                                                                                                   └──Label: label
                                                                                                                   └──Label argument type:
                                                                                                                      └──Type expr: Constructor: string
                                                                                                                   └──Label type:
                                                                                                                      └──Type expr: Constructor: field
                                                                                                                         └──Type expr: Variable: 658
                                                                                                                         └──Type expr: Variable: 576
                                                                                                                         └──Type expr: Variable: 662
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Constructor: string
                                                                                                       └──Desc: Variable
                                                                                                          └──Variable: label
                                                                                              └──Expression:
                                                                                                 └──Type expr: Constructor: unit
                                                                                                 └──Desc: Application
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Constructor: exn
                                                                                                          └──Type expr: Constructor: unit
                                                                                                       └──Desc: Variable
                                                                                                          └──Variable: raise
                                                                                                          └──Type expr: Constructor: unit
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Constructor: exn
                                                                                                       └──Desc: Construct
                                                                                                          └──Constructor description:
                                                                                                             └──Name: Variant_mismatch
                                                                                                             └──Constructor type:
                                                                                                                └──Type expr: Constructor: exn
                                                                                              └──Expression:
                                                                                                 └──Type expr: Constructor: unit
                                                                                                 └──Desc: Constant: ()
                                                                                        └──Expression:
                                                                                           └──Type expr: Constructor: unit
                                                                                           └──Desc: Application
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Variable: 662
                                                                                                    └──Type expr: Constructor: unit
                                                                                                 └──Desc: Application
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Variable: 576
                                                                                                          └──Type expr: Arrow
                                                                                                             └──Type expr: Variable: 662
                                                                                                             └──Type expr: Constructor: unit
                                                                                                       └──Desc: Field
                                                                                                          └──Expression:
                                                                                                             └──Type expr: Constructor: field
                                                                                                                └──Type expr: Variable: 658
                                                                                                                └──Type expr: Variable: 576
                                                                                                                └──Type expr: Variable: 662
                                                                                                             └──Desc: Variable
                                                                                                                └──Variable: field
                                                                                                          └──Label description:
                                                                                                             └──Label: set
                                                                                                             └──Label argument type:
                                                                                                                └──Type expr: Arrow
                                                                                                                   └──Type expr: Variable: 576
                                                                                                                   └──Type expr: Arrow
                                                                                                                      └──Type expr: Variable: 662
                                                                                                                      └──Type expr: Constructor: unit
                                                                                                             └──Label type:
                                                                                                                └──Type expr: Constructor: field
                                                                                                                   └──Type expr: Variable: 658
                                                                                                                   └──Type expr: Variable: 576
                                                                                                                   └──Type expr: Variable: 662
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Variable: 576
                                                                                                       └──Desc: Variable
                                                                                                          └──Variable: builder
                                                                                              └──Expression:
                                                                                                 └──Type expr: Variable: 662
                                                                                                 └──Desc: Application
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Constructor: variant
                                                                                                          └──Type expr: Variable: 662
                                                                                                       └──Desc: Application
                                                                                                          └──Expression:
                                                                                                             └──Type expr: Arrow
                                                                                                                └──Type expr: Constructor: ty
                                                                                                                   └──Type expr: Variable: 662
                                                                                                                └──Type expr: Arrow
                                                                                                                   └──Type expr: Constructor: variant
                                                                                                                   └──Type expr: Variable: 662
                                                                                                             └──Desc: Variable
                                                                                                                └──Variable: devariantize
                                                                                                                └──Type expr: Variable: 662
                                                                                                          └──Expression:
                                                                                                             └──Type expr: Constructor: ty
                                                                                                                └──Type expr: Variable: 662
                                                                                                             └──Desc: Field
                                                                                                                └──Expression:
                                                                                                                   └──Type expr: Constructor: field
                                                                                                                      └──Type expr: Variable: 658
                                                                                                                      └──Type expr: Variable: 576
                                                                                                                      └──Type expr: Variable: 662
                                                                                                                   └──Desc: Variable
                                                                                                                      └──Variable: field
                                                                                                                └──Label description:
                                                                                                                   └──Label: type_
                                                                                                                   └──Label argument type:
                                                                                                                      └──Type expr: Constructor: ty
                                                                                                                         └──Type expr: Variable: 662
                                                                                                                   └──Label type:
                                                                                                                      └──Type expr: Constructor: field
                                                                                                                         └──Type expr: Variable: 658
                                                                                                                         └──Type expr: Variable: 576
                                                                                                                         └──Type expr: Variable: 662
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Constructor: variant
                                                                                                       └──Desc: Variable
                                                                                                          └──Variable: v
                                                             └──Expression:
                                                                └──Type expr: Variable: 384
                                                                └──Desc: Sequence
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: unit
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: packed_field
                                                                                     └──Type expr: Variable: 384
                                                                                     └──Type expr: Variable: 576
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Constructor: string
                                                                                        └──Type expr: Constructor: variant
                                                                                     └──Type expr: Constructor: unit
                                                                               └──Type expr: Constructor: unit
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: list
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Constructor: string
                                                                                           └──Type expr: Constructor: variant
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Constructor: packed_field
                                                                                              └──Type expr: Variable: 384
                                                                                              └──Type expr: Variable: 576
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Constructor: string
                                                                                                 └──Type expr: Constructor: variant
                                                                                              └──Type expr: Constructor: unit
                                                                                        └──Type expr: Constructor: unit
                                                                                  └──Desc: Application
                                                                                     └──Expression:
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Constructor: list
                                                                                              └──Type expr: Constructor: packed_field
                                                                                                 └──Type expr: Variable: 384
                                                                                                 └──Type expr: Variable: 576
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Constructor: list
                                                                                                 └──Type expr: Tuple
                                                                                                    └──Type expr: Constructor: string
                                                                                                    └──Type expr: Constructor: variant
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Constructor: packed_field
                                                                                                       └──Type expr: Variable: 384
                                                                                                       └──Type expr: Variable: 576
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Constructor: string
                                                                                                          └──Type expr: Constructor: variant
                                                                                                       └──Type expr: Constructor: unit
                                                                                                 └──Type expr: Constructor: unit
                                                                                        └──Desc: Variable
                                                                                           └──Variable: iter2
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Constructor: string
                                                                                              └──Type expr: Constructor: variant
                                                                                           └──Type expr: Constructor: packed_field
                                                                                              └──Type expr: Variable: 384
                                                                                              └──Type expr: Variable: 576
                                                                                     └──Expression:
                                                                                        └──Type expr: Constructor: list
                                                                                           └──Type expr: Constructor: packed_field
                                                                                              └──Type expr: Variable: 384
                                                                                              └──Type expr: Variable: 576
                                                                                        └──Desc: Field
                                                                                           └──Expression:
                                                                                              └──Type expr: Constructor: record
                                                                                                 └──Type expr: Variable: 384
                                                                                                 └──Type expr: Variable: 576
                                                                                              └──Desc: Variable
                                                                                                 └──Variable: record
                                                                                           └──Label description:
                                                                                              └──Label: fields
                                                                                              └──Label argument type:
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: packed_field
                                                                                                       └──Type expr: Variable: 384
                                                                                                       └──Type expr: Variable: 576
                                                                                              └──Label type:
                                                                                                 └──Type expr: Constructor: record
                                                                                                    └──Type expr: Variable: 384
                                                                                                    └──Type expr: Variable: 576
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: list
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Constructor: string
                                                                                        └──Type expr: Constructor: variant
                                                                                  └──Desc: Variable
                                                                                     └──Variable: vfields
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: packed_field
                                                                                  └──Type expr: Variable: 384
                                                                                  └──Type expr: Variable: 576
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Constructor: string
                                                                                     └──Type expr: Constructor: variant
                                                                                  └──Type expr: Constructor: unit
                                                                            └──Desc: Variable
                                                                               └──Variable: f
                                                                               └──Type expr: Variable: 384
                                                                   └──Expression:
                                                                      └──Type expr: Variable: 384
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Variable: 576
                                                                               └──Type expr: Variable: 384
                                                                            └──Desc: Field
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: record
                                                                                     └──Type expr: Variable: 384
                                                                                     └──Type expr: Variable: 576
                                                                                  └──Desc: Variable
                                                                                     └──Variable: record
                                                                               └──Label description:
                                                                                  └──Label: of_builder
                                                                                  └──Label argument type:
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Variable: 576
                                                                                        └──Type expr: Variable: 384
                                                                                  └──Label type:
                                                                                     └──Type expr: Constructor: record
                                                                                        └──Type expr: Variable: 384
                                                                                        └──Type expr: Variable: 576
                                                                         └──Expression:
                                                                            └──Type expr: Variable: 576
                                                                            └──Desc: Variable
                                                                               └──Variable: builder
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 384
                                                 └──Type expr: Constructor: variant
                                              └──Desc: Any
                                           └──Expression:
                                              └──Type expr: Variable: 384
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: exn
                                                       └──Type expr: Variable: 384
                                                    └──Desc: Variable
                                                       └──Variable: raise
                                                       └──Type expr: Variable: 384
                                                 └──Expression:
                                                    └──Type expr: Constructor: exn
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Variant_mismatch
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: exn |}]
