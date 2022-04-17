open! Import
open Util

(* Examples from  https://caml.inria.fr/pub/papers/garrigue-polymorphic_variants-ml98.pdf *)

let%expect_test "" =
  let str = 
    {|
      let a = `Apple;;

      let b = `Orange "spain";;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Variant
                      └──Type expr: Row cons
                         └──Label: Apple
                         └──Type expr: Constructor: present
                            └──Type expr: Constructor: unit
                         └──Type expr: Variable: 24124
                   └──Desc: Variable: a
                └──Abstraction:
                   └──Variables: 24124
                   └──Expression:
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Apple
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: unit
                            └──Type expr: Variable: 24124
                      └──Desc: Variant
                         └──Variant description:
                            └──Tag: Apple
                            └──Variant row:
                               └──Type expr: Row cons
                                  └──Label: Apple
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Variable: 24124
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Variant
                      └──Type expr: Row cons
                         └──Label: Orange
                         └──Type expr: Constructor: present
                            └──Type expr: Constructor: string
                         └──Type expr: Variable: 24136
                   └──Desc: Variable: b
                └──Abstraction:
                   └──Variables: 24136
                   └──Expression:
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Orange
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: string
                            └──Type expr: Variable: 24136
                      └──Desc: Variant
                         └──Variant description:
                            └──Tag: Orange
                            └──Variant row:
                               └──Type expr: Row cons
                                  └──Label: Orange
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: string
                                  └──Type expr: Variable: 24136
                         └──Expression:
                            └──Type expr: Constructor: string
                            └──Desc: Constant: spain |}]

let%expect_test "" =
  let str = 
    {|
      let a = `Apple;;
      let b = `Orange "spain";;

      type 'a list = 
        | Nil
        | Cons of 'a * 'a list
      ;;

      let l = Cons (a, Cons (b, Nil));;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Variant
                      └──Type expr: Row cons
                         └──Label: Apple
                         └──Type expr: Constructor: present
                            └──Type expr: Constructor: unit
                         └──Type expr: Variable: 24153
                   └──Desc: Variable: a
                └──Abstraction:
                   └──Variables: 24153
                   └──Expression:
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Apple
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: unit
                            └──Type expr: Variable: 24153
                      └──Desc: Variant
                         └──Variant description:
                            └──Tag: Apple
                            └──Variant row:
                               └──Type expr: Row cons
                                  └──Label: Apple
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Variable: 24153
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Variant
                      └──Type expr: Row cons
                         └──Label: Orange
                         └──Type expr: Constructor: present
                            └──Type expr: Constructor: string
                         └──Type expr: Variable: 24165
                   └──Desc: Variable: b
                └──Abstraction:
                   └──Variables: 24165
                   └──Expression:
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Orange
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: string
                            └──Type expr: Variable: 24165
                      └──Desc: Variant
                         └──Variant description:
                            └──Tag: Orange
                            └──Variant row:
                               └──Type expr: Row cons
                                  └──Label: Orange
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: string
                                  └──Type expr: Variable: 24165
                         └──Expression:
                            └──Type expr: Constructor: string
                            └──Desc: Constant: spain
       └──Structure item: Type
          └──Type declaration:
             └──Type name: list
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: 24146
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 24146
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 24146
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 24146
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: 24146
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 24146
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: list
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Apple
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: unit
                            └──Type expr: Row cons
                               └──Label: Orange
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: string
                               └──Type expr: Variable: 24208
                   └──Desc: Variable: l
                └──Abstraction:
                   └──Variables: 24208
                   └──Expression:
                      └──Type expr: Constructor: list
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Apple
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Row cons
                                  └──Label: Orange
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: string
                                  └──Type expr: Variable: 24208
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: Cons
                            └──Constructor argument type:
                               └──Type expr: Tuple
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Apple
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: Orange
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: string
                                           └──Type expr: Variable: 24208
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Apple
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row cons
                                              └──Label: Orange
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: string
                                              └──Type expr: Variable: 24208
                            └──Constructor type:
                               └──Type expr: Constructor: list
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Apple
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: Orange
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: string
                                           └──Type expr: Variable: 24208
                         └──Expression:
                            └──Type expr: Tuple
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Apple
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row cons
                                        └──Label: Orange
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: string
                                        └──Type expr: Variable: 24208
                               └──Type expr: Constructor: list
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Apple
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: Orange
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: string
                                           └──Type expr: Variable: 24208
                            └──Desc: Tuple
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Apple
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: Orange
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: string
                                           └──Type expr: Variable: 24208
                                  └──Desc: Variable
                                     └──Variable: a
                                     └──Type expr: Row cons
                                        └──Label: Orange
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: string
                                        └──Type expr: Variable: 24208
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Apple
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row cons
                                              └──Label: Orange
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: string
                                              └──Type expr: Variable: 24208
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Cons
                                        └──Constructor argument type:
                                           └──Type expr: Tuple
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Apple
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Orange
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: string
                                                       └──Type expr: Variable: 24208
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Apple
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Orange
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: string
                                                          └──Type expr: Variable: 24208
                                        └──Constructor type:
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Apple
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Orange
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: string
                                                       └──Type expr: Variable: 24208
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Apple
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Orange
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: string
                                                    └──Type expr: Variable: 24208
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Apple
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Orange
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: string
                                                       └──Type expr: Variable: 24208
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Apple
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Orange
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: string
                                                       └──Type expr: Variable: 24208
                                              └──Desc: Variable
                                                 └──Variable: b
                                                 └──Type expr: Row cons
                                                    └──Label: Apple
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Variable: 24208
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Apple
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Orange
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: string
                                                          └──Type expr: Variable: 24208
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Apple
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Orange
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: string
                                                                   └──Type expr: Variable: 24208 |}]

let%expect_test "" =
  let str =
    {|
      external concat : string -> string -> string = "%concat";;

      let show = 
        fun x ->
          match x with
          ( `Apple -> "apple"
          | `Orange s -> concat "orange" s
          )
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
      Structure:
      └──Structure:
         └──Structure item: Primitive
            └──Value description:
               └──Name: concat
               └──Scheme:
                  └──Variables:
                  └──Type expr: Arrow
                     └──Type expr: Constructor: string
                     └──Type expr: Arrow
                        └──Type expr: Constructor: string
                        └──Type expr: Constructor: string
               └──Primitive name: %concat
         └──Structure item: Let
            └──Value bindings:
               └──Value binding:
                  └──Pattern:
                     └──Type expr: Arrow
                        └──Type expr: Variant
                           └──Type expr: Row cons
                              └──Label: Apple
                              └──Type expr: Constructor: present
                                 └──Type expr: Constructor: unit
                              └──Type expr: Row cons
                                 └──Label: Orange
                                 └──Type expr: Constructor: present
                                    └──Type expr: Constructor: string
                                 └──Type expr: Row uniform
                                    └──Type expr: Constructor: absent
                        └──Type expr: Constructor: string
                     └──Desc: Variable: show
                  └──Abstraction:
                     └──Variables:
                     └──Expression:
                        └──Type expr: Arrow
                           └──Type expr: Variant
                              └──Type expr: Row cons
                                 └──Label: Apple
                                 └──Type expr: Constructor: present
                                    └──Type expr: Constructor: unit
                                 └──Type expr: Row cons
                                    └──Label: Orange
                                    └──Type expr: Constructor: present
                                       └──Type expr: Constructor: string
                                    └──Type expr: Row uniform
                                       └──Type expr: Constructor: absent
                           └──Type expr: Constructor: string
                        └──Desc: Function
                           └──Pattern:
                              └──Type expr: Variant
                                 └──Type expr: Row cons
                                    └──Label: Apple
                                    └──Type expr: Constructor: present
                                       └──Type expr: Constructor: unit
                                    └──Type expr: Row cons
                                       └──Label: Orange
                                       └──Type expr: Constructor: present
                                          └──Type expr: Constructor: string
                                       └──Type expr: Row uniform
                                          └──Type expr: Constructor: absent
                              └──Desc: Variable: x
                           └──Expression:
                              └──Type expr: Constructor: string
                              └──Desc: Match
                                 └──Expression:
                                    └──Type expr: Variant
                                       └──Type expr: Row cons
                                          └──Label: Apple
                                          └──Type expr: Constructor: present
                                             └──Type expr: Constructor: unit
                                          └──Type expr: Row cons
                                             └──Label: Orange
                                             └──Type expr: Constructor: present
                                                └──Type expr: Constructor: string
                                             └──Type expr: Row uniform
                                                └──Type expr: Constructor: absent
                                    └──Desc: Variable
                                       └──Variable: x
                                 └──Type expr: Variant
                                    └──Type expr: Row cons
                                       └──Label: Apple
                                       └──Type expr: Constructor: present
                                          └──Type expr: Constructor: unit
                                       └──Type expr: Row cons
                                          └──Label: Orange
                                          └──Type expr: Constructor: present
                                             └──Type expr: Constructor: string
                                          └──Type expr: Row uniform
                                             └──Type expr: Constructor: absent
                                 └──Cases:
                                    └──Case:
                                       └──Pattern:
                                          └──Type expr: Variant
                                             └──Type expr: Row cons
                                                └──Label: Apple
                                                └──Type expr: Constructor: present
                                                   └──Type expr: Constructor: unit
                                                └──Type expr: Row cons
                                                   └──Label: Orange
                                                   └──Type expr: Constructor: present
                                                      └──Type expr: Constructor: string
                                                   └──Type expr: Row uniform
                                                      └──Type expr: Constructor: absent
                                          └──Desc: Variant
                                             └──Variant description:
                                                └──Tag: Apple
                                                └──Variant row:
                                                   └──Type expr: Row cons
                                                      └──Label: Apple
                                                      └──Type expr: Constructor: present
                                                         └──Type expr: Constructor: unit
                                                      └──Type expr: Row cons
                                                         └──Label: Orange
                                                         └──Type expr: Constructor: present
                                                            └──Type expr: Constructor: string
                                                         └──Type expr: Row uniform
                                                            └──Type expr: Constructor: absent
                                       └──Expression:
                                          └──Type expr: Constructor: string
                                          └──Desc: Constant: apple
                                    └──Case:
                                       └──Pattern:
                                          └──Type expr: Variant
                                             └──Type expr: Row cons
                                                └──Label: Apple
                                                └──Type expr: Constructor: present
                                                   └──Type expr: Constructor: unit
                                                └──Type expr: Row cons
                                                   └──Label: Orange
                                                   └──Type expr: Constructor: present
                                                      └──Type expr: Constructor: string
                                                   └──Type expr: Row uniform
                                                      └──Type expr: Constructor: absent
                                          └──Desc: Variant
                                             └──Variant description:
                                                └──Tag: Orange
                                                └──Variant row:
                                                   └──Type expr: Row cons
                                                      └──Label: Apple
                                                      └──Type expr: Constructor: present
                                                         └──Type expr: Constructor: unit
                                                      └──Type expr: Row cons
                                                         └──Label: Orange
                                                         └──Type expr: Constructor: present
                                                            └──Type expr: Constructor: string
                                                         └──Type expr: Row uniform
                                                            └──Type expr: Constructor: absent
                                             └──Pattern:
                                                └──Type expr: Constructor: string
                                                └──Desc: Variable: s
                                       └──Expression:
                                          └──Type expr: Constructor: string
                                          └──Desc: Application
                                             └──Expression:
                                                └──Type expr: Arrow
                                                   └──Type expr: Constructor: string
                                                   └──Type expr: Constructor: string
                                                └──Desc: Application
                                                   └──Expression:
                                                      └──Type expr: Arrow
                                                         └──Type expr: Constructor: string
                                                         └──Type expr: Arrow
                                                            └──Type expr: Constructor: string
                                                            └──Type expr: Constructor: string
                                                      └──Desc: Variable
                                                         └──Variable: concat
                                                   └──Expression:
                                                      └──Type expr: Constructor: string
                                                      └──Desc: Constant: orange
                                             └──Expression:
                                                └──Type expr: Constructor: string
                                                └──Desc: Variable
                                                   └──Variable: s |}]

let%expect_test "" =
  let str = 
    {|
      external concat : string -> string -> string = "%concat";;

      let show = 
        fun x ->
          match x with
          ( `Apple -> "apple"
          | `Orange s -> concat "orange" s
          )
      ;;

      let show' = 
        fun x ->
          match x with
          ( `Apple -> "apple"
          | `Pair -> "pair"
          )
      ;;

      (* Dromedary doesn't support OCaml's subtyping as shown here 
         -- a problem with using rows over precense information   
      *)
      let show_both = 
        fun (x : [< `Apple ]) -> (show x, show' x)
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    ("Cannot unify types"
     ("Type_expr.decode type_expr1"
      (Type 24417
       (Former
        (Variant
         (Type 24422
          (Row_cons Apple
           (Type 24428
            (Former (Constr ((Type 24429 (Former (Constr () unit)))) present)))
           (Type 24423
            (Row_cons Orange
             (Type 24426
              (Former
               (Constr ((Type 24427 (Former (Constr () string)))) present)))
             (Type 24424 (Row_uniform (Type 24425 (Former (Constr () absent)))))))))))))
     ("Type_expr.decode type_expr2"
      (Type 24431
       (Former
        (Variant
         (Type 24432
          (Row_cons Apple
           (Type 24428
            (Former (Constr ((Type 24429 (Former (Constr () unit)))) present)))
           (Type 24433 (Row_uniform (Type 24434 (Former (Constr () absent)))))))))))) |}]

let%expect_test "" =
  let str =
    {|
      let rec map = fun t f ->
        match t with
        ( `Nil -> `Nil
        | `Cons (x, t) -> `Cons (f x, map t f)
        )
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
      Structure:
      └──Structure:
         └──Structure item: Let
            └──Value bindings:
               └──Value binding:
                  └──Variable: map
                  └──Abstraction:
                     └──Variables: 24497,24501
                     └──Expression:
                        └──Type expr: Arrow
                           └──Type expr: Mu
                              └──Variable: 24507
                              └──Type expr: Variant
                                 └──Type expr: Row cons
                                    └──Label: Nil
                                    └──Type expr: Constructor: present
                                       └──Type expr: Constructor: unit
                                    └──Type expr: Row cons
                                       └──Label: Cons
                                       └──Type expr: Constructor: present
                                          └──Type expr: Tuple
                                             └──Type expr: Variable: 24501
                                             └──Type expr: Variable: 24507
                                       └──Type expr: Row uniform
                                          └──Type expr: Constructor: absent
                           └──Type expr: Arrow
                              └──Type expr: Arrow
                                 └──Type expr: Variable: 24501
                                 └──Type expr: Variable: 24497
                              └──Type expr: Mu
                                 └──Variable: 24498
                                 └──Type expr: Variant
                                    └──Type expr: Row cons
                                       └──Label: Cons
                                       └──Type expr: Constructor: present
                                          └──Type expr: Tuple
                                             └──Type expr: Variable: 24497
                                             └──Type expr: Variable: 24498
                                       └──Type expr: Row cons
                                          └──Label: Nil
                                          └──Type expr: Constructor: present
                                             └──Type expr: Constructor: unit
                                          └──Type expr: Variable: 24512
                        └──Desc: Function
                           └──Pattern:
                              └──Type expr: Mu
                                 └──Variable: 24507
                                 └──Type expr: Variant
                                    └──Type expr: Row cons
                                       └──Label: Nil
                                       └──Type expr: Constructor: present
                                          └──Type expr: Constructor: unit
                                       └──Type expr: Row cons
                                          └──Label: Cons
                                          └──Type expr: Constructor: present
                                             └──Type expr: Tuple
                                                └──Type expr: Variable: 24501
                                                └──Type expr: Variable: 24507
                                          └──Type expr: Row uniform
                                             └──Type expr: Constructor: absent
                              └──Desc: Variable: t
                           └──Expression:
                              └──Type expr: Arrow
                                 └──Type expr: Arrow
                                    └──Type expr: Variable: 24501
                                    └──Type expr: Variable: 24497
                                 └──Type expr: Mu
                                    └──Variable: 24498
                                    └──Type expr: Variant
                                       └──Type expr: Row cons
                                          └──Label: Cons
                                          └──Type expr: Constructor: present
                                             └──Type expr: Tuple
                                                └──Type expr: Variable: 24497
                                                └──Type expr: Variable: 24498
                                          └──Type expr: Row cons
                                             └──Label: Nil
                                             └──Type expr: Constructor: present
                                                └──Type expr: Constructor: unit
                                             └──Type expr: Variable: 24512
                              └──Desc: Function
                                 └──Pattern:
                                    └──Type expr: Arrow
                                       └──Type expr: Variable: 24501
                                       └──Type expr: Variable: 24497
                                    └──Desc: Variable: f
                                 └──Expression:
                                    └──Type expr: Mu
                                       └──Variable: 24498
                                       └──Type expr: Variant
                                          └──Type expr: Row cons
                                             └──Label: Cons
                                             └──Type expr: Constructor: present
                                                └──Type expr: Tuple
                                                   └──Type expr: Variable: 24497
                                                   └──Type expr: Variable: 24498
                                             └──Type expr: Row cons
                                                └──Label: Nil
                                                └──Type expr: Constructor: present
                                                   └──Type expr: Constructor: unit
                                                └──Type expr: Variable: 24512
                                    └──Desc: Match
                                       └──Expression:
                                          └──Type expr: Mu
                                             └──Variable: 24507
                                             └──Type expr: Variant
                                                └──Type expr: Row cons
                                                   └──Label: Nil
                                                   └──Type expr: Constructor: present
                                                      └──Type expr: Constructor: unit
                                                   └──Type expr: Row cons
                                                      └──Label: Cons
                                                      └──Type expr: Constructor: present
                                                         └──Type expr: Tuple
                                                            └──Type expr: Variable: 24501
                                                            └──Type expr: Variable: 24507
                                                      └──Type expr: Row uniform
                                                         └──Type expr: Constructor: absent
                                          └──Desc: Variable
                                             └──Variable: t
                                       └──Type expr: Mu
                                          └──Variable: 24507
                                          └──Type expr: Variant
                                             └──Type expr: Row cons
                                                └──Label: Nil
                                                └──Type expr: Constructor: present
                                                   └──Type expr: Constructor: unit
                                                └──Type expr: Row cons
                                                   └──Label: Cons
                                                   └──Type expr: Constructor: present
                                                      └──Type expr: Tuple
                                                         └──Type expr: Variable: 24501
                                                         └──Type expr: Variable: 24507
                                                   └──Type expr: Row uniform
                                                      └──Type expr: Constructor: absent
                                       └──Cases:
                                          └──Case:
                                             └──Pattern:
                                                └──Type expr: Variant
                                                   └──Type expr: Row cons
                                                      └──Label: Nil
                                                      └──Type expr: Constructor: present
                                                         └──Type expr: Constructor: unit
                                                      └──Type expr: Row cons
                                                         └──Label: Cons
                                                         └──Type expr: Constructor: present
                                                            └──Type expr: Mu
                                                               └──Variable: 24451
                                                               └──Type expr: Tuple
                                                                  └──Type expr: Variable: 24501
                                                                  └──Type expr: Variant
                                                                     └──Type expr: Row cons
                                                                        └──Label: Nil
                                                                        └──Type expr: Constructor: present
                                                                           └──Type expr: Constructor: unit
                                                                        └──Type expr: Row cons
                                                                           └──Label: Cons
                                                                           └──Type expr: Constructor: present
                                                                              └──Type expr: Variable: 24451
                                                                           └──Type expr: Row uniform
                                                                              └──Type expr: Constructor: absent
                                                         └──Type expr: Row uniform
                                                            └──Type expr: Constructor: absent
                                                └──Desc: Variant
                                                   └──Variant description:
                                                      └──Tag: Nil
                                                      └──Variant row:
                                                         └──Type expr: Row cons
                                                            └──Label: Nil
                                                            └──Type expr: Constructor: present
                                                               └──Type expr: Constructor: unit
                                                            └──Type expr: Row cons
                                                               └──Label: Cons
                                                               └──Type expr: Constructor: present
                                                                  └──Type expr: Mu
                                                                     └──Variable: 24451
                                                                     └──Type expr: Tuple
                                                                        └──Type expr: Variable: 24501
                                                                        └──Type expr: Variant
                                                                           └──Type expr: Row cons
                                                                              └──Label: Nil
                                                                              └──Type expr: Constructor: present
                                                                                 └──Type expr: Constructor: unit
                                                                              └──Type expr: Row cons
                                                                                 └──Label: Cons
                                                                                 └──Type expr: Constructor: present
                                                                                    └──Type expr: Variable: 24451
                                                                                 └──Type expr: Row uniform
                                                                                    └──Type expr: Constructor: absent
                                                               └──Type expr: Row uniform
                                                                  └──Type expr: Constructor: absent
                                             └──Expression:
                                                └──Type expr: Mu
                                                   └──Variable: 24498
                                                   └──Type expr: Variant
                                                      └──Type expr: Row cons
                                                         └──Label: Cons
                                                         └──Type expr: Constructor: present
                                                            └──Type expr: Tuple
                                                               └──Type expr: Variable: 24497
                                                               └──Type expr: Variable: 24498
                                                         └──Type expr: Row cons
                                                            └──Label: Nil
                                                            └──Type expr: Constructor: present
                                                               └──Type expr: Constructor: unit
                                                            └──Type expr: Variable: 24512
                                                └──Desc: Variant
                                                   └──Variant description:
                                                      └──Tag: Nil
                                                      └──Variant row:
                                                         └──Type expr: Mu
                                                            └──Variable: 24475
                                                            └──Type expr: Row cons
                                                               └──Label: Cons
                                                               └──Type expr: Constructor: present
                                                                  └──Type expr: Tuple
                                                                     └──Type expr: Variable: 24497
                                                                     └──Type expr: Variant
                                                                        └──Type expr: Variable: 24475
                                                               └──Type expr: Row cons
                                                                  └──Label: Nil
                                                                  └──Type expr: Constructor: present
                                                                     └──Type expr: Constructor: unit
                                                                  └──Type expr: Variable: 24512
                                          └──Case:
                                             └──Pattern:
                                                └──Type expr: Variant
                                                   └──Type expr: Row cons
                                                      └──Label: Nil
                                                      └──Type expr: Constructor: present
                                                         └──Type expr: Constructor: unit
                                                      └──Type expr: Row cons
                                                         └──Label: Cons
                                                         └──Type expr: Constructor: present
                                                            └──Type expr: Mu
                                                               └──Variable: 24451
                                                               └──Type expr: Tuple
                                                                  └──Type expr: Variable: 24501
                                                                  └──Type expr: Variant
                                                                     └──Type expr: Row cons
                                                                        └──Label: Nil
                                                                        └──Type expr: Constructor: present
                                                                           └──Type expr: Constructor: unit
                                                                        └──Type expr: Row cons
                                                                           └──Label: Cons
                                                                           └──Type expr: Constructor: present
                                                                              └──Type expr: Variable: 24451
                                                                           └──Type expr: Row uniform
                                                                              └──Type expr: Constructor: absent
                                                         └──Type expr: Row uniform
                                                            └──Type expr: Constructor: absent
                                                └──Desc: Variant
                                                   └──Variant description:
                                                      └──Tag: Cons
                                                      └──Variant row:
                                                         └──Type expr: Row cons
                                                            └──Label: Nil
                                                            └──Type expr: Constructor: present
                                                               └──Type expr: Constructor: unit
                                                            └──Type expr: Row cons
                                                               └──Label: Cons
                                                               └──Type expr: Constructor: present
                                                                  └──Type expr: Mu
                                                                     └──Variable: 24451
                                                                     └──Type expr: Tuple
                                                                        └──Type expr: Variable: 24501
                                                                        └──Type expr: Variant
                                                                           └──Type expr: Row cons
                                                                              └──Label: Nil
                                                                              └──Type expr: Constructor: present
                                                                                 └──Type expr: Constructor: unit
                                                                              └──Type expr: Row cons
                                                                                 └──Label: Cons
                                                                                 └──Type expr: Constructor: present
                                                                                    └──Type expr: Variable: 24451
                                                                                 └──Type expr: Row uniform
                                                                                    └──Type expr: Constructor: absent
                                                               └──Type expr: Row uniform
                                                                  └──Type expr: Constructor: absent
                                                   └──Pattern:
                                                      └──Type expr: Mu
                                                         └──Variable: 24451
                                                         └──Type expr: Tuple
                                                            └──Type expr: Variable: 24501
                                                            └──Type expr: Variant
                                                               └──Type expr: Row cons
                                                                  └──Label: Nil
                                                                  └──Type expr: Constructor: present
                                                                     └──Type expr: Constructor: unit
                                                                  └──Type expr: Row cons
                                                                     └──Label: Cons
                                                                     └──Type expr: Constructor: present
                                                                        └──Type expr: Variable: 24451
                                                                     └──Type expr: Row uniform
                                                                        └──Type expr: Constructor: absent
                                                      └──Desc: Tuple
                                                         └──Pattern:
                                                            └──Type expr: Variable: 24501
                                                            └──Desc: Variable: x
                                                         └──Pattern:
                                                            └──Type expr: Mu
                                                               └──Variable: 24507
                                                               └──Type expr: Variant
                                                                  └──Type expr: Row cons
                                                                     └──Label: Nil
                                                                     └──Type expr: Constructor: present
                                                                        └──Type expr: Constructor: unit
                                                                     └──Type expr: Row cons
                                                                        └──Label: Cons
                                                                        └──Type expr: Constructor: present
                                                                           └──Type expr: Tuple
                                                                              └──Type expr: Variable: 24501
                                                                              └──Type expr: Variable: 24507
                                                                        └──Type expr: Row uniform
                                                                           └──Type expr: Constructor: absent
                                                            └──Desc: Variable: t
                                             └──Expression:
                                                └──Type expr: Mu
                                                   └──Variable: 24498
                                                   └──Type expr: Variant
                                                      └──Type expr: Row cons
                                                         └──Label: Cons
                                                         └──Type expr: Constructor: present
                                                            └──Type expr: Tuple
                                                               └──Type expr: Variable: 24497
                                                               └──Type expr: Variable: 24498
                                                         └──Type expr: Row cons
                                                            └──Label: Nil
                                                            └──Type expr: Constructor: present
                                                               └──Type expr: Constructor: unit
                                                            └──Type expr: Variable: 24512
                                                └──Desc: Variant
                                                   └──Variant description:
                                                      └──Tag: Cons
                                                      └──Variant row:
                                                         └──Type expr: Mu
                                                            └──Variable: 24475
                                                            └──Type expr: Row cons
                                                               └──Label: Cons
                                                               └──Type expr: Constructor: present
                                                                  └──Type expr: Tuple
                                                                     └──Type expr: Variable: 24497
                                                                     └──Type expr: Variant
                                                                        └──Type expr: Variable: 24475
                                                               └──Type expr: Row cons
                                                                  └──Label: Nil
                                                                  └──Type expr: Constructor: present
                                                                     └──Type expr: Constructor: unit
                                                                  └──Type expr: Variable: 24512
                                                   └──Expression:
                                                      └──Type expr: Mu
                                                         └──Variable: 24492
                                                         └──Type expr: Tuple
                                                            └──Type expr: Variable: 24497
                                                            └──Type expr: Variant
                                                               └──Type expr: Row cons
                                                                  └──Label: Cons
                                                                  └──Type expr: Constructor: present
                                                                     └──Type expr: Variable: 24492
                                                                  └──Type expr: Row cons
                                                                     └──Label: Nil
                                                                     └──Type expr: Constructor: present
                                                                        └──Type expr: Constructor: unit
                                                                     └──Type expr: Variable: 24512
                                                      └──Desc: Tuple
                                                         └──Expression:
                                                            └──Type expr: Variable: 24497
                                                            └──Desc: Application
                                                               └──Expression:
                                                                  └──Type expr: Arrow
                                                                     └──Type expr: Variable: 24501
                                                                     └──Type expr: Variable: 24497
                                                                  └──Desc: Variable
                                                                     └──Variable: f
                                                               └──Expression:
                                                                  └──Type expr: Variable: 24501
                                                                  └──Desc: Variable
                                                                     └──Variable: x
                                                         └──Expression:
                                                            └──Type expr: Mu
                                                               └──Variable: 24498
                                                               └──Type expr: Variant
                                                                  └──Type expr: Row cons
                                                                     └──Label: Cons
                                                                     └──Type expr: Constructor: present
                                                                        └──Type expr: Tuple
                                                                           └──Type expr: Variable: 24497
                                                                           └──Type expr: Variable: 24498
                                                                     └──Type expr: Row cons
                                                                        └──Label: Nil
                                                                        └──Type expr: Constructor: present
                                                                           └──Type expr: Constructor: unit
                                                                        └──Type expr: Variable: 24512
                                                            └──Desc: Application
                                                               └──Expression:
                                                                  └──Type expr: Arrow
                                                                     └──Type expr: Arrow
                                                                        └──Type expr: Variable: 24501
                                                                        └──Type expr: Variable: 24497
                                                                     └──Type expr: Mu
                                                                        └──Variable: 24498
                                                                        └──Type expr: Variant
                                                                           └──Type expr: Row cons
                                                                              └──Label: Cons
                                                                              └──Type expr: Constructor: present
                                                                                 └──Type expr: Tuple
                                                                                    └──Type expr: Variable: 24497
                                                                                    └──Type expr: Variable: 24498
                                                                              └──Type expr: Row cons
                                                                                 └──Label: Nil
                                                                                 └──Type expr: Constructor: present
                                                                                    └──Type expr: Constructor: unit
                                                                                 └──Type expr: Variable: 24512
                                                                  └──Desc: Application
                                                                     └──Expression:
                                                                        └──Type expr: Arrow
                                                                           └──Type expr: Mu
                                                                              └──Variable: 24507
                                                                              └──Type expr: Variant
                                                                                 └──Type expr: Row cons
                                                                                    └──Label: Nil
                                                                                    └──Type expr: Constructor: present
                                                                                       └──Type expr: Constructor: unit
                                                                                    └──Type expr: Row cons
                                                                                       └──Label: Cons
                                                                                       └──Type expr: Constructor: present
                                                                                          └──Type expr: Tuple
                                                                                             └──Type expr: Variable: 24501
                                                                                             └──Type expr: Variable: 24507
                                                                                       └──Type expr: Row uniform
                                                                                          └──Type expr: Constructor: absent
                                                                           └──Type expr: Arrow
                                                                              └──Type expr: Arrow
                                                                                 └──Type expr: Variable: 24501
                                                                                 └──Type expr: Variable: 24497
                                                                              └──Type expr: Mu
                                                                                 └──Variable: 24498
                                                                                 └──Type expr: Variant
                                                                                    └──Type expr: Row cons
                                                                                       └──Label: Cons
                                                                                       └──Type expr: Constructor: present
                                                                                          └──Type expr: Tuple
                                                                                             └──Type expr: Variable: 24497
                                                                                             └──Type expr: Variable: 24498
                                                                                       └──Type expr: Row cons
                                                                                          └──Label: Nil
                                                                                          └──Type expr: Constructor: present
                                                                                             └──Type expr: Constructor: unit
                                                                                          └──Type expr: Variable: 24512
                                                                        └──Desc: Variable
                                                                           └──Variable: map
                                                                     └──Expression:
                                                                        └──Type expr: Mu
                                                                           └──Variable: 24507
                                                                           └──Type expr: Variant
                                                                              └──Type expr: Row cons
                                                                                 └──Label: Nil
                                                                                 └──Type expr: Constructor: present
                                                                                    └──Type expr: Constructor: unit
                                                                                 └──Type expr: Row cons
                                                                                    └──Label: Cons
                                                                                    └──Type expr: Constructor: present
                                                                                       └──Type expr: Tuple
                                                                                          └──Type expr: Variable: 24501
                                                                                          └──Type expr: Variable: 24507
                                                                                    └──Type expr: Row uniform
                                                                                       └──Type expr: Constructor: absent
                                                                        └──Desc: Variable
                                                                           └──Variable: t
                                                               └──Expression:
                                                                  └──Type expr: Arrow
                                                                     └──Type expr: Variable: 24501
                                                                     └──Type expr: Variable: 24497
                                                                  └──Desc: Variable
                                                                     └──Variable: f |}]

let%expect_test "" =
  let str = 
    {|
      external concat : string -> string -> string = "%concat";;

      let show = 
        fun x ->
          match x with
          ( `Apple -> "apple"
          | `Orange s -> concat "orange" s
          | _ -> "pair"
          )
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Primitive
          └──Value description:
             └──Name: concat
             └──Scheme:
                └──Variables:
                └──Type expr: Arrow
                   └──Type expr: Constructor: string
                   └──Type expr: Arrow
                      └──Type expr: Constructor: string
                      └──Type expr: Constructor: string
             └──Primitive name: %concat
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Apple
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: unit
                            └──Type expr: Row cons
                               └──Label: Orange
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: string
                               └──Type expr: Variable: 24536
                      └──Type expr: Constructor: string
                   └──Desc: Variable: show
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Apple
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Row cons
                                  └──Label: Orange
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: string
                                  └──Type expr: Variable: 24536
                         └──Type expr: Constructor: string
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Apple
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Row cons
                                     └──Label: Orange
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: string
                                     └──Type expr: Variable: 24536
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: string
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Apple
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: Orange
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: string
                                           └──Type expr: Variable: 24536
                                  └──Desc: Variable
                                     └──Variable: x
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Apple
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row cons
                                        └──Label: Orange
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: string
                                        └──Type expr: Variable: 24536
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Apple
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Orange
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: string
                                                 └──Type expr: Variable: 24536
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Apple
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: Apple
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Orange
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: string
                                                       └──Type expr: Variable: 24536
                                     └──Expression:
                                        └──Type expr: Constructor: string
                                        └──Desc: Constant: apple
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Apple
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Orange
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: string
                                                 └──Type expr: Variable: 24536
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Orange
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: Apple
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Orange
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: string
                                                       └──Type expr: Variable: 24536
                                           └──Pattern:
                                              └──Type expr: Constructor: string
                                              └──Desc: Variable: s
                                     └──Expression:
                                        └──Type expr: Constructor: string
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: string
                                                 └──Type expr: Constructor: string
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: string
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: string
                                                          └──Type expr: Constructor: string
                                                    └──Desc: Variable
                                                       └──Variable: concat
                                                 └──Expression:
                                                    └──Type expr: Constructor: string
                                                    └──Desc: Constant: orange
                                           └──Expression:
                                              └──Type expr: Constructor: string
                                              └──Desc: Variable
                                                 └──Variable: s
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Apple
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Orange
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: string
                                                 └──Type expr: Variable: 24536
                                        └──Desc: Any
                                     └──Expression:
                                        └──Type expr: Constructor: string
                                        └──Desc: Constant: pair |}]

let%expect_test "" =
  let str = 
    {|
      type 'a list = 
        | Nil
        | Cons of 'a * 'a list
      ;;

      external append : 'a. 'a list -> 'a list -> 'a list = "%append";;

      let a = Cons (`Orange "morocco", Cons (`Apple, Nil));;
      let b = Cons (`Apple, Cons (`Pear, Nil));;
      let c = append a b;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: list
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: 24580
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 24580
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 24580
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 24580
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: 24580
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 24580
       └──Structure item: Primitive
          └──Value description:
             └──Name: append
             └──Scheme:
                └──Variables: 24585
                └──Type expr: Arrow
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: 24585
                   └──Type expr: Arrow
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 24585
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 24585
             └──Primitive name: %append
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: list
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Apple
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: unit
                            └──Type expr: Row cons
                               └──Label: Orange
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: string
                               └──Type expr: Variable: 24641
                   └──Desc: Variable: a
                └──Abstraction:
                   └──Variables: 24641
                   └──Expression:
                      └──Type expr: Constructor: list
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Apple
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Row cons
                                  └──Label: Orange
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: string
                                  └──Type expr: Variable: 24641
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: Cons
                            └──Constructor argument type:
                               └──Type expr: Tuple
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Apple
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: Orange
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: string
                                           └──Type expr: Variable: 24641
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Apple
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row cons
                                              └──Label: Orange
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: string
                                              └──Type expr: Variable: 24641
                            └──Constructor type:
                               └──Type expr: Constructor: list
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Apple
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: Orange
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: string
                                           └──Type expr: Variable: 24641
                         └──Expression:
                            └──Type expr: Tuple
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Apple
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row cons
                                        └──Label: Orange
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: string
                                        └──Type expr: Variable: 24641
                               └──Type expr: Constructor: list
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Apple
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: Orange
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: string
                                           └──Type expr: Variable: 24641
                            └──Desc: Tuple
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Apple
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: Orange
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: string
                                           └──Type expr: Variable: 24641
                                  └──Desc: Variant
                                     └──Variant description:
                                        └──Tag: Orange
                                        └──Variant row:
                                           └──Type expr: Row cons
                                              └──Label: Apple
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Orange
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: string
                                                 └──Type expr: Variable: 24641
                                     └──Expression:
                                        └──Type expr: Constructor: string
                                        └──Desc: Constant: morocco
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Apple
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row cons
                                              └──Label: Orange
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: string
                                              └──Type expr: Variable: 24641
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Cons
                                        └──Constructor argument type:
                                           └──Type expr: Tuple
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Apple
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Orange
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: string
                                                       └──Type expr: Variable: 24641
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Apple
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Orange
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: string
                                                          └──Type expr: Variable: 24641
                                        └──Constructor type:
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Apple
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Orange
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: string
                                                       └──Type expr: Variable: 24641
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Apple
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Orange
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: string
                                                    └──Type expr: Variable: 24641
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Apple
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Orange
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: string
                                                       └──Type expr: Variable: 24641
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Apple
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Orange
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: string
                                                       └──Type expr: Variable: 24641
                                              └──Desc: Variant
                                                 └──Variant description:
                                                    └──Tag: Apple
                                                    └──Variant row:
                                                       └──Type expr: Row cons
                                                          └──Label: Apple
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Orange
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: string
                                                             └──Type expr: Variable: 24641
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Apple
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Orange
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: string
                                                          └──Type expr: Variable: 24641
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Apple
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Orange
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: string
                                                                   └──Type expr: Variable: 24641
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: list
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Apple
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: unit
                            └──Type expr: Row cons
                               └──Label: Pear
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Variable: 24692
                   └──Desc: Variable: b
                └──Abstraction:
                   └──Variables: 24692
                   └──Expression:
                      └──Type expr: Constructor: list
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Apple
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Row cons
                                  └──Label: Pear
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Variable: 24692
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: Cons
                            └──Constructor argument type:
                               └──Type expr: Tuple
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Apple
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: Pear
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: 24692
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Apple
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row cons
                                              └──Label: Pear
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Variable: 24692
                            └──Constructor type:
                               └──Type expr: Constructor: list
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Apple
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: Pear
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: 24692
                         └──Expression:
                            └──Type expr: Tuple
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Apple
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row cons
                                        └──Label: Pear
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Variable: 24692
                               └──Type expr: Constructor: list
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Apple
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: Pear
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: 24692
                            └──Desc: Tuple
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Apple
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: Pear
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: 24692
                                  └──Desc: Variant
                                     └──Variant description:
                                        └──Tag: Apple
                                        └──Variant row:
                                           └──Type expr: Row cons
                                              └──Label: Apple
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Pear
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Variable: 24692
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Apple
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row cons
                                              └──Label: Pear
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Variable: 24692
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Cons
                                        └──Constructor argument type:
                                           └──Type expr: Tuple
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Apple
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Pear
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Variable: 24692
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Apple
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Pear
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Variable: 24692
                                        └──Constructor type:
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Apple
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Pear
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Variable: 24692
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Apple
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Pear
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Variable: 24692
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Apple
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Pear
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Variable: 24692
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Apple
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Pear
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Variable: 24692
                                              └──Desc: Variant
                                                 └──Variant description:
                                                    └──Tag: Pear
                                                    └──Variant row:
                                                       └──Type expr: Row cons
                                                          └──Label: Apple
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Pear
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: 24692
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Apple
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Pear
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Variable: 24692
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Apple
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Pear
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: 24692
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: list
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Apple
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: unit
                            └──Type expr: Row cons
                               └──Label: Orange
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: string
                               └──Type expr: Row cons
                                  └──Label: Pear
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Variable: 24729
                   └──Desc: Variable: c
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: list
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Apple
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Row cons
                                  └──Label: Orange
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: string
                                  └──Type expr: Row cons
                                     └──Label: Pear
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Variable: 24729
                      └──Desc: Application
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: list
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Apple
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: Orange
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: string
                                           └──Type expr: Row cons
                                              └──Label: Pear
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Variable: 24729
                               └──Type expr: Constructor: list
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Apple
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: Orange
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: string
                                           └──Type expr: Row cons
                                              └──Label: Pear
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Variable: 24729
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Apple
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Orange
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: string
                                                 └──Type expr: Row cons
                                                    └──Label: Pear
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Variable: 24729
                                     └──Type expr: Arrow
                                        └──Type expr: Constructor: list
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Apple
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Orange
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: string
                                                    └──Type expr: Row cons
                                                       └──Label: Pear
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Variable: 24729
                                        └──Type expr: Constructor: list
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Apple
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Orange
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: string
                                                    └──Type expr: Row cons
                                                       └──Label: Pear
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Variable: 24729
                                  └──Desc: Variable
                                     └──Variable: append
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Apple
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row cons
                                              └──Label: Orange
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: string
                                              └──Type expr: Row cons
                                                 └──Label: Pear
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Variable: 24729
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Apple
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row cons
                                              └──Label: Orange
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: string
                                              └──Type expr: Row cons
                                                 └──Label: Pear
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Variable: 24729
                                  └──Desc: Variable
                                     └──Variable: a
                                     └──Type expr: Row cons
                                        └──Label: Pear
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Variable: 24729
                         └──Expression:
                            └──Type expr: Constructor: list
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Apple
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row cons
                                        └──Label: Orange
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: string
                                        └──Type expr: Row cons
                                           └──Label: Pear
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: 24729
                            └──Desc: Variable
                               └──Variable: b
                               └──Type expr: Row cons
                                  └──Label: Orange
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: string
                                  └──Type expr: Variable: 24729 |}]