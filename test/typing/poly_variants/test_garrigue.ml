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
                         └──Type expr: Variable: 2
                   └──Desc: Variable: a
                └──Abstraction:
                   └──Variables: 2
                   └──Expression:
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Apple
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: unit
                            └──Type expr: Variable: 2
                      └──Desc: Variant
                         └──Variant description:
                            └──Tag: Apple
                            └──Variant row:
                               └──Type expr: Row cons
                                  └──Label: Apple
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Variable: 2
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Variant
                      └──Type expr: Row cons
                         └──Label: Orange
                         └──Type expr: Constructor: present
                            └──Type expr: Constructor: string
                         └──Type expr: Variable: 14
                   └──Desc: Variable: b
                └──Abstraction:
                   └──Variables: 14
                   └──Expression:
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Orange
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: string
                            └──Type expr: Variable: 14
                      └──Desc: Variant
                         └──Variant description:
                            └──Tag: Orange
                            └──Variant row:
                               └──Type expr: Row cons
                                  └──Label: Orange
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: string
                                  └──Type expr: Variable: 14
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
                         └──Type expr: Variable: 2
                   └──Desc: Variable: a
                └──Abstraction:
                   └──Variables: 2
                   └──Expression:
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Apple
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: unit
                            └──Type expr: Variable: 2
                      └──Desc: Variant
                         └──Variant description:
                            └──Tag: Apple
                            └──Variant row:
                               └──Type expr: Row cons
                                  └──Label: Apple
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Variable: 2
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Variant
                      └──Type expr: Row cons
                         └──Label: Orange
                         └──Type expr: Constructor: present
                            └──Type expr: Constructor: string
                         └──Type expr: Variable: 14
                   └──Desc: Variable: b
                └──Abstraction:
                   └──Variables: 14
                   └──Expression:
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Orange
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: string
                            └──Type expr: Variable: 14
                      └──Desc: Variant
                         └──Variant description:
                            └──Tag: Orange
                            └──Variant row:
                               └──Type expr: Row cons
                                  └──Label: Orange
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: string
                                  └──Type expr: Variable: 14
                         └──Expression:
                            └──Type expr: Constructor: string
                            └──Desc: Constant: spain
       └──Structure item: Type
          └──Type declaration:
             └──Type name: list
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: 24
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 24
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 24
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 24
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: 24
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 24
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
                               └──Type expr: Variable: 57
                   └──Desc: Variable: l
                └──Abstraction:
                   └──Variables: 57
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
                                  └──Type expr: Variable: 57
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
                                           └──Type expr: Variable: 57
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
                                              └──Type expr: Variable: 57
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
                                           └──Type expr: Variable: 57
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
                                        └──Type expr: Variable: 57
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
                                           └──Type expr: Variable: 57
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
                                           └──Type expr: Variable: 57
                                  └──Desc: Variable
                                     └──Variable: a
                                     └──Type expr: Row cons
                                        └──Label: Orange
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: string
                                        └──Type expr: Variable: 57
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
                                              └──Type expr: Variable: 57
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
                                                       └──Type expr: Variable: 57
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
                                                          └──Type expr: Variable: 57
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
                                                       └──Type expr: Variable: 57
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
                                                    └──Type expr: Variable: 57
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
                                                       └──Type expr: Variable: 57
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
                                                       └──Type expr: Variable: 57
                                              └──Desc: Variable
                                                 └──Variable: b
                                                 └──Type expr: Row cons
                                                    └──Label: Apple
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Variable: 57
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
                                                          └──Type expr: Variable: 57
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
                                                                   └──Type expr: Variable: 57 |}]

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
      (Type 140
       (Former
        (Variant
         (Type 145
          (Row_cons Apple
           (Type 151
            (Former (Constr ((Type 152 (Former (Constr () unit)))) present)))
           (Type 146
            (Row_cons Orange
             (Type 149
              (Former (Constr ((Type 150 (Former (Constr () string)))) present)))
             (Type 147 (Row_uniform (Type 148 (Former (Constr () absent)))))))))))))
     ("Type_expr.decode type_expr2"
      (Type 154
       (Former
        (Variant
         (Type 155
          (Row_cons Apple
           (Type 151
            (Former (Constr ((Type 152 (Former (Constr () unit)))) present)))
           (Type 156 (Row_uniform (Type 157 (Former (Constr () absent)))))))))))) |}]

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
                     └──Variables: 60,64
                     └──Expression:
                        └──Type expr: Arrow
                           └──Type expr: Mu
                              └──Variable: 70
                              └──Type expr: Variant
                                 └──Type expr: Row cons
                                    └──Label: Nil
                                    └──Type expr: Constructor: present
                                       └──Type expr: Constructor: unit
                                    └──Type expr: Row cons
                                       └──Label: Cons
                                       └──Type expr: Constructor: present
                                          └──Type expr: Tuple
                                             └──Type expr: Variable: 64
                                             └──Type expr: Variable: 70
                                       └──Type expr: Row uniform
                                          └──Type expr: Constructor: absent
                           └──Type expr: Arrow
                              └──Type expr: Arrow
                                 └──Type expr: Variable: 64
                                 └──Type expr: Variable: 60
                              └──Type expr: Mu
                                 └──Variable: 61
                                 └──Type expr: Variant
                                    └──Type expr: Row cons
                                       └──Label: Cons
                                       └──Type expr: Constructor: present
                                          └──Type expr: Tuple
                                             └──Type expr: Variable: 60
                                             └──Type expr: Variable: 61
                                       └──Type expr: Row cons
                                          └──Label: Nil
                                          └──Type expr: Constructor: present
                                             └──Type expr: Constructor: unit
                                          └──Type expr: Variable: 75
                        └──Desc: Function
                           └──Pattern:
                              └──Type expr: Mu
                                 └──Variable: 70
                                 └──Type expr: Variant
                                    └──Type expr: Row cons
                                       └──Label: Nil
                                       └──Type expr: Constructor: present
                                          └──Type expr: Constructor: unit
                                       └──Type expr: Row cons
                                          └──Label: Cons
                                          └──Type expr: Constructor: present
                                             └──Type expr: Tuple
                                                └──Type expr: Variable: 64
                                                └──Type expr: Variable: 70
                                          └──Type expr: Row uniform
                                             └──Type expr: Constructor: absent
                              └──Desc: Variable: t
                           └──Expression:
                              └──Type expr: Arrow
                                 └──Type expr: Arrow
                                    └──Type expr: Variable: 64
                                    └──Type expr: Variable: 60
                                 └──Type expr: Mu
                                    └──Variable: 61
                                    └──Type expr: Variant
                                       └──Type expr: Row cons
                                          └──Label: Cons
                                          └──Type expr: Constructor: present
                                             └──Type expr: Tuple
                                                └──Type expr: Variable: 60
                                                └──Type expr: Variable: 61
                                          └──Type expr: Row cons
                                             └──Label: Nil
                                             └──Type expr: Constructor: present
                                                └──Type expr: Constructor: unit
                                             └──Type expr: Variable: 75
                              └──Desc: Function
                                 └──Pattern:
                                    └──Type expr: Arrow
                                       └──Type expr: Variable: 64
                                       └──Type expr: Variable: 60
                                    └──Desc: Variable: f
                                 └──Expression:
                                    └──Type expr: Mu
                                       └──Variable: 61
                                       └──Type expr: Variant
                                          └──Type expr: Row cons
                                             └──Label: Cons
                                             └──Type expr: Constructor: present
                                                └──Type expr: Tuple
                                                   └──Type expr: Variable: 60
                                                   └──Type expr: Variable: 61
                                             └──Type expr: Row cons
                                                └──Label: Nil
                                                └──Type expr: Constructor: present
                                                   └──Type expr: Constructor: unit
                                                └──Type expr: Variable: 75
                                    └──Desc: Match
                                       └──Expression:
                                          └──Type expr: Mu
                                             └──Variable: 70
                                             └──Type expr: Variant
                                                └──Type expr: Row cons
                                                   └──Label: Nil
                                                   └──Type expr: Constructor: present
                                                      └──Type expr: Constructor: unit
                                                   └──Type expr: Row cons
                                                      └──Label: Cons
                                                      └──Type expr: Constructor: present
                                                         └──Type expr: Tuple
                                                            └──Type expr: Variable: 64
                                                            └──Type expr: Variable: 70
                                                      └──Type expr: Row uniform
                                                         └──Type expr: Constructor: absent
                                          └──Desc: Variable
                                             └──Variable: t
                                       └──Type expr: Mu
                                          └──Variable: 70
                                          └──Type expr: Variant
                                             └──Type expr: Row cons
                                                └──Label: Nil
                                                └──Type expr: Constructor: present
                                                   └──Type expr: Constructor: unit
                                                └──Type expr: Row cons
                                                   └──Label: Cons
                                                   └──Type expr: Constructor: present
                                                      └──Type expr: Tuple
                                                         └──Type expr: Variable: 64
                                                         └──Type expr: Variable: 70
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
                                                               └──Variable: 14
                                                               └──Type expr: Tuple
                                                                  └──Type expr: Variable: 64
                                                                  └──Type expr: Variant
                                                                     └──Type expr: Row cons
                                                                        └──Label: Nil
                                                                        └──Type expr: Constructor: present
                                                                           └──Type expr: Constructor: unit
                                                                        └──Type expr: Row cons
                                                                           └──Label: Cons
                                                                           └──Type expr: Constructor: present
                                                                              └──Type expr: Variable: 14
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
                                                                     └──Variable: 14
                                                                     └──Type expr: Tuple
                                                                        └──Type expr: Variable: 64
                                                                        └──Type expr: Variant
                                                                           └──Type expr: Row cons
                                                                              └──Label: Nil
                                                                              └──Type expr: Constructor: present
                                                                                 └──Type expr: Constructor: unit
                                                                              └──Type expr: Row cons
                                                                                 └──Label: Cons
                                                                                 └──Type expr: Constructor: present
                                                                                    └──Type expr: Variable: 14
                                                                                 └──Type expr: Row uniform
                                                                                    └──Type expr: Constructor: absent
                                                               └──Type expr: Row uniform
                                                                  └──Type expr: Constructor: absent
                                             └──Expression:
                                                └──Type expr: Mu
                                                   └──Variable: 61
                                                   └──Type expr: Variant
                                                      └──Type expr: Row cons
                                                         └──Label: Cons
                                                         └──Type expr: Constructor: present
                                                            └──Type expr: Tuple
                                                               └──Type expr: Variable: 60
                                                               └──Type expr: Variable: 61
                                                         └──Type expr: Row cons
                                                            └──Label: Nil
                                                            └──Type expr: Constructor: present
                                                               └──Type expr: Constructor: unit
                                                            └──Type expr: Variable: 75
                                                └──Desc: Variant
                                                   └──Variant description:
                                                      └──Tag: Nil
                                                      └──Variant row:
                                                         └──Type expr: Mu
                                                            └──Variable: 38
                                                            └──Type expr: Row cons
                                                               └──Label: Cons
                                                               └──Type expr: Constructor: present
                                                                  └──Type expr: Tuple
                                                                     └──Type expr: Variable: 60
                                                                     └──Type expr: Variant
                                                                        └──Type expr: Variable: 38
                                                               └──Type expr: Row cons
                                                                  └──Label: Nil
                                                                  └──Type expr: Constructor: present
                                                                     └──Type expr: Constructor: unit
                                                                  └──Type expr: Variable: 75
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
                                                               └──Variable: 14
                                                               └──Type expr: Tuple
                                                                  └──Type expr: Variable: 64
                                                                  └──Type expr: Variant
                                                                     └──Type expr: Row cons
                                                                        └──Label: Nil
                                                                        └──Type expr: Constructor: present
                                                                           └──Type expr: Constructor: unit
                                                                        └──Type expr: Row cons
                                                                           └──Label: Cons
                                                                           └──Type expr: Constructor: present
                                                                              └──Type expr: Variable: 14
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
                                                                     └──Variable: 14
                                                                     └──Type expr: Tuple
                                                                        └──Type expr: Variable: 64
                                                                        └──Type expr: Variant
                                                                           └──Type expr: Row cons
                                                                              └──Label: Nil
                                                                              └──Type expr: Constructor: present
                                                                                 └──Type expr: Constructor: unit
                                                                              └──Type expr: Row cons
                                                                                 └──Label: Cons
                                                                                 └──Type expr: Constructor: present
                                                                                    └──Type expr: Variable: 14
                                                                                 └──Type expr: Row uniform
                                                                                    └──Type expr: Constructor: absent
                                                               └──Type expr: Row uniform
                                                                  └──Type expr: Constructor: absent
                                                   └──Pattern:
                                                      └──Type expr: Mu
                                                         └──Variable: 14
                                                         └──Type expr: Tuple
                                                            └──Type expr: Variable: 64
                                                            └──Type expr: Variant
                                                               └──Type expr: Row cons
                                                                  └──Label: Nil
                                                                  └──Type expr: Constructor: present
                                                                     └──Type expr: Constructor: unit
                                                                  └──Type expr: Row cons
                                                                     └──Label: Cons
                                                                     └──Type expr: Constructor: present
                                                                        └──Type expr: Variable: 14
                                                                     └──Type expr: Row uniform
                                                                        └──Type expr: Constructor: absent
                                                      └──Desc: Tuple
                                                         └──Pattern:
                                                            └──Type expr: Variable: 64
                                                            └──Desc: Variable: x
                                                         └──Pattern:
                                                            └──Type expr: Mu
                                                               └──Variable: 70
                                                               └──Type expr: Variant
                                                                  └──Type expr: Row cons
                                                                     └──Label: Nil
                                                                     └──Type expr: Constructor: present
                                                                        └──Type expr: Constructor: unit
                                                                     └──Type expr: Row cons
                                                                        └──Label: Cons
                                                                        └──Type expr: Constructor: present
                                                                           └──Type expr: Tuple
                                                                              └──Type expr: Variable: 64
                                                                              └──Type expr: Variable: 70
                                                                        └──Type expr: Row uniform
                                                                           └──Type expr: Constructor: absent
                                                            └──Desc: Variable: t
                                             └──Expression:
                                                └──Type expr: Mu
                                                   └──Variable: 61
                                                   └──Type expr: Variant
                                                      └──Type expr: Row cons
                                                         └──Label: Cons
                                                         └──Type expr: Constructor: present
                                                            └──Type expr: Tuple
                                                               └──Type expr: Variable: 60
                                                               └──Type expr: Variable: 61
                                                         └──Type expr: Row cons
                                                            └──Label: Nil
                                                            └──Type expr: Constructor: present
                                                               └──Type expr: Constructor: unit
                                                            └──Type expr: Variable: 75
                                                └──Desc: Variant
                                                   └──Variant description:
                                                      └──Tag: Cons
                                                      └──Variant row:
                                                         └──Type expr: Mu
                                                            └──Variable: 38
                                                            └──Type expr: Row cons
                                                               └──Label: Cons
                                                               └──Type expr: Constructor: present
                                                                  └──Type expr: Tuple
                                                                     └──Type expr: Variable: 60
                                                                     └──Type expr: Variant
                                                                        └──Type expr: Variable: 38
                                                               └──Type expr: Row cons
                                                                  └──Label: Nil
                                                                  └──Type expr: Constructor: present
                                                                     └──Type expr: Constructor: unit
                                                                  └──Type expr: Variable: 75
                                                   └──Expression:
                                                      └──Type expr: Mu
                                                         └──Variable: 55
                                                         └──Type expr: Tuple
                                                            └──Type expr: Variable: 60
                                                            └──Type expr: Variant
                                                               └──Type expr: Row cons
                                                                  └──Label: Cons
                                                                  └──Type expr: Constructor: present
                                                                     └──Type expr: Variable: 55
                                                                  └──Type expr: Row cons
                                                                     └──Label: Nil
                                                                     └──Type expr: Constructor: present
                                                                        └──Type expr: Constructor: unit
                                                                     └──Type expr: Variable: 75
                                                      └──Desc: Tuple
                                                         └──Expression:
                                                            └──Type expr: Variable: 60
                                                            └──Desc: Application
                                                               └──Expression:
                                                                  └──Type expr: Arrow
                                                                     └──Type expr: Variable: 64
                                                                     └──Type expr: Variable: 60
                                                                  └──Desc: Variable
                                                                     └──Variable: f
                                                               └──Expression:
                                                                  └──Type expr: Variable: 64
                                                                  └──Desc: Variable
                                                                     └──Variable: x
                                                         └──Expression:
                                                            └──Type expr: Mu
                                                               └──Variable: 61
                                                               └──Type expr: Variant
                                                                  └──Type expr: Row cons
                                                                     └──Label: Cons
                                                                     └──Type expr: Constructor: present
                                                                        └──Type expr: Tuple
                                                                           └──Type expr: Variable: 60
                                                                           └──Type expr: Variable: 61
                                                                     └──Type expr: Row cons
                                                                        └──Label: Nil
                                                                        └──Type expr: Constructor: present
                                                                           └──Type expr: Constructor: unit
                                                                        └──Type expr: Variable: 75
                                                            └──Desc: Application
                                                               └──Expression:
                                                                  └──Type expr: Arrow
                                                                     └──Type expr: Arrow
                                                                        └──Type expr: Variable: 64
                                                                        └──Type expr: Variable: 60
                                                                     └──Type expr: Mu
                                                                        └──Variable: 61
                                                                        └──Type expr: Variant
                                                                           └──Type expr: Row cons
                                                                              └──Label: Cons
                                                                              └──Type expr: Constructor: present
                                                                                 └──Type expr: Tuple
                                                                                    └──Type expr: Variable: 60
                                                                                    └──Type expr: Variable: 61
                                                                              └──Type expr: Row cons
                                                                                 └──Label: Nil
                                                                                 └──Type expr: Constructor: present
                                                                                    └──Type expr: Constructor: unit
                                                                                 └──Type expr: Variable: 75
                                                                  └──Desc: Application
                                                                     └──Expression:
                                                                        └──Type expr: Arrow
                                                                           └──Type expr: Mu
                                                                              └──Variable: 70
                                                                              └──Type expr: Variant
                                                                                 └──Type expr: Row cons
                                                                                    └──Label: Nil
                                                                                    └──Type expr: Constructor: present
                                                                                       └──Type expr: Constructor: unit
                                                                                    └──Type expr: Row cons
                                                                                       └──Label: Cons
                                                                                       └──Type expr: Constructor: present
                                                                                          └──Type expr: Tuple
                                                                                             └──Type expr: Variable: 64
                                                                                             └──Type expr: Variable: 70
                                                                                       └──Type expr: Row uniform
                                                                                          └──Type expr: Constructor: absent
                                                                           └──Type expr: Arrow
                                                                              └──Type expr: Arrow
                                                                                 └──Type expr: Variable: 64
                                                                                 └──Type expr: Variable: 60
                                                                              └──Type expr: Mu
                                                                                 └──Variable: 61
                                                                                 └──Type expr: Variant
                                                                                    └──Type expr: Row cons
                                                                                       └──Label: Cons
                                                                                       └──Type expr: Constructor: present
                                                                                          └──Type expr: Tuple
                                                                                             └──Type expr: Variable: 60
                                                                                             └──Type expr: Variable: 61
                                                                                       └──Type expr: Row cons
                                                                                          └──Label: Nil
                                                                                          └──Type expr: Constructor: present
                                                                                             └──Type expr: Constructor: unit
                                                                                          └──Type expr: Variable: 75
                                                                        └──Desc: Variable
                                                                           └──Variable: map
                                                                     └──Expression:
                                                                        └──Type expr: Mu
                                                                           └──Variable: 70
                                                                           └──Type expr: Variant
                                                                              └──Type expr: Row cons
                                                                                 └──Label: Nil
                                                                                 └──Type expr: Constructor: present
                                                                                    └──Type expr: Constructor: unit
                                                                                 └──Type expr: Row cons
                                                                                    └──Label: Cons
                                                                                    └──Type expr: Constructor: present
                                                                                       └──Type expr: Tuple
                                                                                          └──Type expr: Variable: 64
                                                                                          └──Type expr: Variable: 70
                                                                                    └──Type expr: Row uniform
                                                                                       └──Type expr: Constructor: absent
                                                                        └──Desc: Variable
                                                                           └──Variable: t
                                                               └──Expression:
                                                                  └──Type expr: Arrow
                                                                     └──Type expr: Variable: 64
                                                                     └──Type expr: Variable: 60
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
                               └──Type expr: Variable: 17
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
                                  └──Type expr: Variable: 17
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
                                     └──Type expr: Variable: 17
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
                                           └──Type expr: Variable: 17
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
                                        └──Type expr: Variable: 17
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
                                                 └──Type expr: Variable: 17
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
                                                       └──Type expr: Variable: 17
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
                                                 └──Type expr: Variable: 17
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
                                                       └──Type expr: Variable: 17
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
                                                 └──Type expr: Variable: 17
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
                   └──Constructor alphas: 61
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 61
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 61
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 61
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: 61
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 61
       └──Structure item: Primitive
          └──Value description:
             └──Name: append
             └──Scheme:
                └──Variables: 0
                └──Type expr: Arrow
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: 0
                   └──Type expr: Arrow
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 0
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 0
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
                               └──Type expr: Variable: 56
                   └──Desc: Variable: a
                └──Abstraction:
                   └──Variables: 56
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
                                  └──Type expr: Variable: 56
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
                                           └──Type expr: Variable: 56
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
                                              └──Type expr: Variable: 56
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
                                           └──Type expr: Variable: 56
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
                                        └──Type expr: Variable: 56
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
                                           └──Type expr: Variable: 56
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
                                           └──Type expr: Variable: 56
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
                                                 └──Type expr: Variable: 56
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
                                              └──Type expr: Variable: 56
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
                                                       └──Type expr: Variable: 56
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
                                                          └──Type expr: Variable: 56
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
                                                       └──Type expr: Variable: 56
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
                                                    └──Type expr: Variable: 56
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
                                                       └──Type expr: Variable: 56
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
                                                       └──Type expr: Variable: 56
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
                                                             └──Type expr: Variable: 56
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
                                                          └──Type expr: Variable: 56
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
                                                                   └──Type expr: Variable: 56
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
                               └──Type expr: Variable: 107
                   └──Desc: Variable: b
                └──Abstraction:
                   └──Variables: 107
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
                                  └──Type expr: Variable: 107
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
                                           └──Type expr: Variable: 107
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
                                              └──Type expr: Variable: 107
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
                                           └──Type expr: Variable: 107
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
                                        └──Type expr: Variable: 107
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
                                           └──Type expr: Variable: 107
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
                                           └──Type expr: Variable: 107
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
                                                 └──Type expr: Variable: 107
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
                                              └──Type expr: Variable: 107
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
                                                       └──Type expr: Variable: 107
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
                                                          └──Type expr: Variable: 107
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
                                                       └──Type expr: Variable: 107
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
                                                    └──Type expr: Variable: 107
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
                                                       └──Type expr: Variable: 107
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
                                                       └──Type expr: Variable: 107
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
                                                             └──Type expr: Variable: 107
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
                                                          └──Type expr: Variable: 107
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
                                                                   └──Type expr: Variable: 107
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
                                  └──Type expr: Variable: 144
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
                                     └──Type expr: Variable: 144
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
                                              └──Type expr: Variable: 144
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
                                              └──Type expr: Variable: 144
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
                                                    └──Type expr: Variable: 144
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
                                                       └──Type expr: Variable: 144
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
                                                       └──Type expr: Variable: 144
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
                                                 └──Type expr: Variable: 144
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
                                                 └──Type expr: Variable: 144
                                  └──Desc: Variable
                                     └──Variable: a
                                     └──Type expr: Row cons
                                        └──Label: Pear
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Variable: 144
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
                                           └──Type expr: Variable: 144
                            └──Desc: Variable
                               └──Variable: b
                               └──Type expr: Row cons
                                  └──Label: Orange
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: string
                                  └──Type expr: Variable: 144 |}]