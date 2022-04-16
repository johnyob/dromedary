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
                         └──Type expr: Variable: a22837
                   └──Desc: Variable: a
                └──Abstraction:
                   └──Variables: a22837
                   └──Expression:
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Apple
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: unit
                            └──Type expr: Variable: a22837
                      └──Desc: Variant
                         └──Variant description:
                            └──Tag: Apple
                            └──Variant row:
                               └──Type expr: Row cons
                                  └──Label: Apple
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Variable: a22837
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Variant
                      └──Type expr: Row cons
                         └──Label: Orange
                         └──Type expr: Constructor: present
                            └──Type expr: Constructor: string
                         └──Type expr: Variable: a22849
                   └──Desc: Variable: b
                └──Abstraction:
                   └──Variables: a22849
                   └──Expression:
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Orange
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: string
                            └──Type expr: Variable: a22849
                      └──Desc: Variant
                         └──Variant description:
                            └──Tag: Orange
                            └──Variant row:
                               └──Type expr: Row cons
                                  └──Label: Orange
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: string
                                  └──Type expr: Variable: a22849
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
                         └──Type expr: Variable: a22861
                   └──Desc: Variable: a
                └──Abstraction:
                   └──Variables: a22861
                   └──Expression:
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Apple
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: unit
                            └──Type expr: Variable: a22861
                      └──Desc: Variant
                         └──Variant description:
                            └──Tag: Apple
                            └──Variant row:
                               └──Type expr: Row cons
                                  └──Label: Apple
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Variable: a22861
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Variant
                      └──Type expr: Row cons
                         └──Label: Orange
                         └──Type expr: Constructor: present
                            └──Type expr: Constructor: string
                         └──Type expr: Variable: a22873
                   └──Desc: Variable: b
                └──Abstraction:
                   └──Variables: a22873
                   └──Expression:
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Orange
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: string
                            └──Type expr: Variable: a22873
                      └──Desc: Variant
                         └──Variant description:
                            └──Tag: Orange
                            └──Variant row:
                               └──Type expr: Row cons
                                  └──Label: Orange
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: string
                                  └──Type expr: Variable: a22873
                         └──Expression:
                            └──Type expr: Constructor: string
                            └──Desc: Constant: spain
       └──Structure item: Type
          └──Type declaration:
             └──Type name: list
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: a
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a
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
                               └──Type expr: Variable: a22916
                   └──Desc: Variable: l
                └──Abstraction:
                   └──Variables: a22916
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
                                  └──Type expr: Variable: a22916
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
                                           └──Type expr: Variable: a22916
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
                                              └──Type expr: Variable: a22916
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
                                           └──Type expr: Variable: a22916
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
                                        └──Type expr: Variable: a22916
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
                                           └──Type expr: Variable: a22916
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
                                           └──Type expr: Variable: a22916
                                  └──Desc: Variable
                                     └──Variable: a
                                     └──Type expr: Row cons
                                        └──Label: Orange
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: string
                                        └──Type expr: Variable: a22916
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
                                              └──Type expr: Variable: a22916
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
                                                       └──Type expr: Variable: a22916
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
                                                          └──Type expr: Variable: a22916
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
                                                       └──Type expr: Variable: a22916
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
                                                    └──Type expr: Variable: a22916
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
                                                       └──Type expr: Variable: a22916
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
                                                       └──Type expr: Variable: a22916
                                              └──Desc: Variable
                                                 └──Variable: b
                                                 └──Type expr: Row cons
                                                    └──Label: Apple
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Variable: a22916
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
                                                          └──Type expr: Variable: a22916
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
                                                                   └──Type expr: Variable: a22916 |}]

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
     (type_expr1
      ((desc
        (Ttyp_variant
         ((desc
           (Ttyp_row_cons Apple
            ((desc (Ttyp_constr ((((desc (Ttyp_constr (() unit))))) present))))
            ((desc
              (Ttyp_row_cons Orange
               ((desc
                 (Ttyp_constr ((((desc (Ttyp_constr (() string))))) present))))
               ((desc (Ttyp_row_uniform ((desc (Ttyp_constr (() absent)))))))))))))))))
     (type_expr2
      ((desc
        (Ttyp_variant
         ((desc
           (Ttyp_row_cons Apple
            ((desc (Ttyp_constr ((((desc (Ttyp_constr (() unit))))) present))))
            ((desc (Ttyp_row_uniform ((desc (Ttyp_constr (() absent))))))))))))))) |}]

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
                     └──Variables: a23205,a23209
                     └──Expression:
                        └──Type expr: Arrow
                           └──Type expr: Mu
                              └──Variable: a23215
                              └──Type expr: Variant
                                 └──Type expr: Row cons
                                    └──Label: Nil
                                    └──Type expr: Constructor: present
                                       └──Type expr: Constructor: unit
                                    └──Type expr: Row cons
                                       └──Label: Cons
                                       └──Type expr: Constructor: present
                                          └──Type expr: Tuple
                                             └──Type expr: Variable: a23209
                                             └──Type expr: Variable: a23215
                                       └──Type expr: Row uniform
                                          └──Type expr: Constructor: absent
                           └──Type expr: Arrow
                              └──Type expr: Arrow
                                 └──Type expr: Variable: a23209
                                 └──Type expr: Variable: a23205
                              └──Type expr: Mu
                                 └──Variable: a23206
                                 └──Type expr: Variant
                                    └──Type expr: Row cons
                                       └──Label: Cons
                                       └──Type expr: Constructor: present
                                          └──Type expr: Tuple
                                             └──Type expr: Variable: a23205
                                             └──Type expr: Variable: a23206
                                       └──Type expr: Row cons
                                          └──Label: Nil
                                          └──Type expr: Constructor: present
                                             └──Type expr: Constructor: unit
                                          └──Type expr: Variable: a23220
                        └──Desc: Function
                           └──Pattern:
                              └──Type expr: Mu
                                 └──Variable: a23215
                                 └──Type expr: Variant
                                    └──Type expr: Row cons
                                       └──Label: Nil
                                       └──Type expr: Constructor: present
                                          └──Type expr: Constructor: unit
                                       └──Type expr: Row cons
                                          └──Label: Cons
                                          └──Type expr: Constructor: present
                                             └──Type expr: Tuple
                                                └──Type expr: Variable: a23209
                                                └──Type expr: Variable: a23215
                                          └──Type expr: Row uniform
                                             └──Type expr: Constructor: absent
                              └──Desc: Variable: t
                           └──Expression:
                              └──Type expr: Arrow
                                 └──Type expr: Arrow
                                    └──Type expr: Variable: a23209
                                    └──Type expr: Variable: a23205
                                 └──Type expr: Mu
                                    └──Variable: a23206
                                    └──Type expr: Variant
                                       └──Type expr: Row cons
                                          └──Label: Cons
                                          └──Type expr: Constructor: present
                                             └──Type expr: Tuple
                                                └──Type expr: Variable: a23205
                                                └──Type expr: Variable: a23206
                                          └──Type expr: Row cons
                                             └──Label: Nil
                                             └──Type expr: Constructor: present
                                                └──Type expr: Constructor: unit
                                             └──Type expr: Variable: a23220
                              └──Desc: Function
                                 └──Pattern:
                                    └──Type expr: Arrow
                                       └──Type expr: Variable: a23209
                                       └──Type expr: Variable: a23205
                                    └──Desc: Variable: f
                                 └──Expression:
                                    └──Type expr: Mu
                                       └──Variable: a23206
                                       └──Type expr: Variant
                                          └──Type expr: Row cons
                                             └──Label: Cons
                                             └──Type expr: Constructor: present
                                                └──Type expr: Tuple
                                                   └──Type expr: Variable: a23205
                                                   └──Type expr: Variable: a23206
                                             └──Type expr: Row cons
                                                └──Label: Nil
                                                └──Type expr: Constructor: present
                                                   └──Type expr: Constructor: unit
                                                └──Type expr: Variable: a23220
                                    └──Desc: Match
                                       └──Expression:
                                          └──Type expr: Mu
                                             └──Variable: a23215
                                             └──Type expr: Variant
                                                └──Type expr: Row cons
                                                   └──Label: Nil
                                                   └──Type expr: Constructor: present
                                                      └──Type expr: Constructor: unit
                                                   └──Type expr: Row cons
                                                      └──Label: Cons
                                                      └──Type expr: Constructor: present
                                                         └──Type expr: Tuple
                                                            └──Type expr: Variable: a23209
                                                            └──Type expr: Variable: a23215
                                                      └──Type expr: Row uniform
                                                         └──Type expr: Constructor: absent
                                          └──Desc: Variable
                                             └──Variable: t
                                       └──Type expr: Mu
                                          └──Variable: a23215
                                          └──Type expr: Variant
                                             └──Type expr: Row cons
                                                └──Label: Nil
                                                └──Type expr: Constructor: present
                                                   └──Type expr: Constructor: unit
                                                └──Type expr: Row cons
                                                   └──Label: Cons
                                                   └──Type expr: Constructor: present
                                                      └──Type expr: Tuple
                                                         └──Type expr: Variable: a23209
                                                         └──Type expr: Variable: a23215
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
                                                               └──Variable: a23159
                                                               └──Type expr: Tuple
                                                                  └──Type expr: Variable: a23209
                                                                  └──Type expr: Variant
                                                                     └──Type expr: Row cons
                                                                        └──Label: Nil
                                                                        └──Type expr: Constructor: present
                                                                           └──Type expr: Constructor: unit
                                                                        └──Type expr: Row cons
                                                                           └──Label: Cons
                                                                           └──Type expr: Constructor: present
                                                                              └──Type expr: Variable: a23159
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
                                                                     └──Variable: a23159
                                                                     └──Type expr: Tuple
                                                                        └──Type expr: Variable: a23209
                                                                        └──Type expr: Variant
                                                                           └──Type expr: Row cons
                                                                              └──Label: Nil
                                                                              └──Type expr: Constructor: present
                                                                                 └──Type expr: Constructor: unit
                                                                              └──Type expr: Row cons
                                                                                 └──Label: Cons
                                                                                 └──Type expr: Constructor: present
                                                                                    └──Type expr: Variable: a23159
                                                                                 └──Type expr: Row uniform
                                                                                    └──Type expr: Constructor: absent
                                                               └──Type expr: Row uniform
                                                                  └──Type expr: Constructor: absent
                                             └──Expression:
                                                └──Type expr: Mu
                                                   └──Variable: a23206
                                                   └──Type expr: Variant
                                                      └──Type expr: Row cons
                                                         └──Label: Cons
                                                         └──Type expr: Constructor: present
                                                            └──Type expr: Tuple
                                                               └──Type expr: Variable: a23205
                                                               └──Type expr: Variable: a23206
                                                         └──Type expr: Row cons
                                                            └──Label: Nil
                                                            └──Type expr: Constructor: present
                                                               └──Type expr: Constructor: unit
                                                            └──Type expr: Variable: a23220
                                                └──Desc: Variant
                                                   └──Variant description:
                                                      └──Tag: Nil
                                                      └──Variant row:
                                                         └──Type expr: Mu
                                                            └──Variable: a23183
                                                            └──Type expr: Row cons
                                                               └──Label: Cons
                                                               └──Type expr: Constructor: present
                                                                  └──Type expr: Tuple
                                                                     └──Type expr: Variable: a23205
                                                                     └──Type expr: Variant
                                                                        └──Type expr: Variable: a23183
                                                               └──Type expr: Row cons
                                                                  └──Label: Nil
                                                                  └──Type expr: Constructor: present
                                                                     └──Type expr: Constructor: unit
                                                                  └──Type expr: Variable: a23220
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
                                                               └──Variable: a23159
                                                               └──Type expr: Tuple
                                                                  └──Type expr: Variable: a23209
                                                                  └──Type expr: Variant
                                                                     └──Type expr: Row cons
                                                                        └──Label: Nil
                                                                        └──Type expr: Constructor: present
                                                                           └──Type expr: Constructor: unit
                                                                        └──Type expr: Row cons
                                                                           └──Label: Cons
                                                                           └──Type expr: Constructor: present
                                                                              └──Type expr: Variable: a23159
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
                                                                     └──Variable: a23159
                                                                     └──Type expr: Tuple
                                                                        └──Type expr: Variable: a23209
                                                                        └──Type expr: Variant
                                                                           └──Type expr: Row cons
                                                                              └──Label: Nil
                                                                              └──Type expr: Constructor: present
                                                                                 └──Type expr: Constructor: unit
                                                                              └──Type expr: Row cons
                                                                                 └──Label: Cons
                                                                                 └──Type expr: Constructor: present
                                                                                    └──Type expr: Variable: a23159
                                                                                 └──Type expr: Row uniform
                                                                                    └──Type expr: Constructor: absent
                                                               └──Type expr: Row uniform
                                                                  └──Type expr: Constructor: absent
                                                   └──Pattern:
                                                      └──Type expr: Mu
                                                         └──Variable: a23159
                                                         └──Type expr: Tuple
                                                            └──Type expr: Variable: a23209
                                                            └──Type expr: Variant
                                                               └──Type expr: Row cons
                                                                  └──Label: Nil
                                                                  └──Type expr: Constructor: present
                                                                     └──Type expr: Constructor: unit
                                                                  └──Type expr: Row cons
                                                                     └──Label: Cons
                                                                     └──Type expr: Constructor: present
                                                                        └──Type expr: Variable: a23159
                                                                     └──Type expr: Row uniform
                                                                        └──Type expr: Constructor: absent
                                                      └──Desc: Tuple
                                                         └──Pattern:
                                                            └──Type expr: Variable: a23209
                                                            └──Desc: Variable: x
                                                         └──Pattern:
                                                            └──Type expr: Mu
                                                               └──Variable: a23215
                                                               └──Type expr: Variant
                                                                  └──Type expr: Row cons
                                                                     └──Label: Nil
                                                                     └──Type expr: Constructor: present
                                                                        └──Type expr: Constructor: unit
                                                                     └──Type expr: Row cons
                                                                        └──Label: Cons
                                                                        └──Type expr: Constructor: present
                                                                           └──Type expr: Tuple
                                                                              └──Type expr: Variable: a23209
                                                                              └──Type expr: Variable: a23215
                                                                        └──Type expr: Row uniform
                                                                           └──Type expr: Constructor: absent
                                                            └──Desc: Variable: t
                                             └──Expression:
                                                └──Type expr: Mu
                                                   └──Variable: a23206
                                                   └──Type expr: Variant
                                                      └──Type expr: Row cons
                                                         └──Label: Cons
                                                         └──Type expr: Constructor: present
                                                            └──Type expr: Tuple
                                                               └──Type expr: Variable: a23205
                                                               └──Type expr: Variable: a23206
                                                         └──Type expr: Row cons
                                                            └──Label: Nil
                                                            └──Type expr: Constructor: present
                                                               └──Type expr: Constructor: unit
                                                            └──Type expr: Variable: a23220
                                                └──Desc: Variant
                                                   └──Variant description:
                                                      └──Tag: Cons
                                                      └──Variant row:
                                                         └──Type expr: Mu
                                                            └──Variable: a23183
                                                            └──Type expr: Row cons
                                                               └──Label: Cons
                                                               └──Type expr: Constructor: present
                                                                  └──Type expr: Tuple
                                                                     └──Type expr: Variable: a23205
                                                                     └──Type expr: Variant
                                                                        └──Type expr: Variable: a23183
                                                               └──Type expr: Row cons
                                                                  └──Label: Nil
                                                                  └──Type expr: Constructor: present
                                                                     └──Type expr: Constructor: unit
                                                                  └──Type expr: Variable: a23220
                                                   └──Expression:
                                                      └──Type expr: Mu
                                                         └──Variable: a23200
                                                         └──Type expr: Tuple
                                                            └──Type expr: Variable: a23205
                                                            └──Type expr: Variant
                                                               └──Type expr: Row cons
                                                                  └──Label: Cons
                                                                  └──Type expr: Constructor: present
                                                                     └──Type expr: Variable: a23200
                                                                  └──Type expr: Row cons
                                                                     └──Label: Nil
                                                                     └──Type expr: Constructor: present
                                                                        └──Type expr: Constructor: unit
                                                                     └──Type expr: Variable: a23220
                                                      └──Desc: Tuple
                                                         └──Expression:
                                                            └──Type expr: Variable: a23205
                                                            └──Desc: Application
                                                               └──Expression:
                                                                  └──Type expr: Arrow
                                                                     └──Type expr: Variable: a23209
                                                                     └──Type expr: Variable: a23205
                                                                  └──Desc: Variable
                                                                     └──Variable: f
                                                               └──Expression:
                                                                  └──Type expr: Variable: a23209
                                                                  └──Desc: Variable
                                                                     └──Variable: x
                                                         └──Expression:
                                                            └──Type expr: Mu
                                                               └──Variable: a23206
                                                               └──Type expr: Variant
                                                                  └──Type expr: Row cons
                                                                     └──Label: Cons
                                                                     └──Type expr: Constructor: present
                                                                        └──Type expr: Tuple
                                                                           └──Type expr: Variable: a23205
                                                                           └──Type expr: Variable: a23206
                                                                     └──Type expr: Row cons
                                                                        └──Label: Nil
                                                                        └──Type expr: Constructor: present
                                                                           └──Type expr: Constructor: unit
                                                                        └──Type expr: Variable: a23220
                                                            └──Desc: Application
                                                               └──Expression:
                                                                  └──Type expr: Arrow
                                                                     └──Type expr: Arrow
                                                                        └──Type expr: Variable: a23209
                                                                        └──Type expr: Variable: a23205
                                                                     └──Type expr: Mu
                                                                        └──Variable: a23206
                                                                        └──Type expr: Variant
                                                                           └──Type expr: Row cons
                                                                              └──Label: Cons
                                                                              └──Type expr: Constructor: present
                                                                                 └──Type expr: Tuple
                                                                                    └──Type expr: Variable: a23205
                                                                                    └──Type expr: Variable: a23206
                                                                              └──Type expr: Row cons
                                                                                 └──Label: Nil
                                                                                 └──Type expr: Constructor: present
                                                                                    └──Type expr: Constructor: unit
                                                                                 └──Type expr: Variable: a23220
                                                                  └──Desc: Application
                                                                     └──Expression:
                                                                        └──Type expr: Arrow
                                                                           └──Type expr: Mu
                                                                              └──Variable: a23215
                                                                              └──Type expr: Variant
                                                                                 └──Type expr: Row cons
                                                                                    └──Label: Nil
                                                                                    └──Type expr: Constructor: present
                                                                                       └──Type expr: Constructor: unit
                                                                                    └──Type expr: Row cons
                                                                                       └──Label: Cons
                                                                                       └──Type expr: Constructor: present
                                                                                          └──Type expr: Tuple
                                                                                             └──Type expr: Variable: a23209
                                                                                             └──Type expr: Variable: a23215
                                                                                       └──Type expr: Row uniform
                                                                                          └──Type expr: Constructor: absent
                                                                           └──Type expr: Arrow
                                                                              └──Type expr: Arrow
                                                                                 └──Type expr: Variable: a23209
                                                                                 └──Type expr: Variable: a23205
                                                                              └──Type expr: Mu
                                                                                 └──Variable: a23206
                                                                                 └──Type expr: Variant
                                                                                    └──Type expr: Row cons
                                                                                       └──Label: Cons
                                                                                       └──Type expr: Constructor: present
                                                                                          └──Type expr: Tuple
                                                                                             └──Type expr: Variable: a23205
                                                                                             └──Type expr: Variable: a23206
                                                                                       └──Type expr: Row cons
                                                                                          └──Label: Nil
                                                                                          └──Type expr: Constructor: present
                                                                                             └──Type expr: Constructor: unit
                                                                                          └──Type expr: Variable: a23220
                                                                        └──Desc: Variable
                                                                           └──Variable: map
                                                                     └──Expression:
                                                                        └──Type expr: Mu
                                                                           └──Variable: a23215
                                                                           └──Type expr: Variant
                                                                              └──Type expr: Row cons
                                                                                 └──Label: Nil
                                                                                 └──Type expr: Constructor: present
                                                                                    └──Type expr: Constructor: unit
                                                                                 └──Type expr: Row cons
                                                                                    └──Label: Cons
                                                                                    └──Type expr: Constructor: present
                                                                                       └──Type expr: Tuple
                                                                                          └──Type expr: Variable: a23209
                                                                                          └──Type expr: Variable: a23215
                                                                                    └──Type expr: Row uniform
                                                                                       └──Type expr: Constructor: absent
                                                                        └──Desc: Variable
                                                                           └──Variable: t
                                                               └──Expression:
                                                                  └──Type expr: Arrow
                                                                     └──Type expr: Variable: a23209
                                                                     └──Type expr: Variable: a23205
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
                               └──Type expr: Variable: a23244
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
                                  └──Type expr: Variable: a23244
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
                                     └──Type expr: Variable: a23244
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
                                           └──Type expr: Variable: a23244
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
                                        └──Type expr: Variable: a23244
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
                                                 └──Type expr: Variable: a23244
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
                                                       └──Type expr: Variable: a23244
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
                                                 └──Type expr: Variable: a23244
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
                                                       └──Type expr: Variable: a23244
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
                                                 └──Type expr: Variable: a23244
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
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: a
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a
       └──Structure item: Primitive
          └──Value description:
             └──Name: append
             └──Scheme:
                └──Variables: a23288
                └──Type expr: Arrow
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: a23288
                   └──Type expr: Arrow
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a23288
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a23288
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
                               └──Type expr: Variable: a23344
                   └──Desc: Variable: a
                └──Abstraction:
                   └──Variables: a23344
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
                                  └──Type expr: Variable: a23344
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
                                           └──Type expr: Variable: a23344
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
                                              └──Type expr: Variable: a23344
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
                                           └──Type expr: Variable: a23344
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
                                        └──Type expr: Variable: a23344
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
                                           └──Type expr: Variable: a23344
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
                                           └──Type expr: Variable: a23344
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
                                                 └──Type expr: Variable: a23344
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
                                              └──Type expr: Variable: a23344
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
                                                       └──Type expr: Variable: a23344
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
                                                          └──Type expr: Variable: a23344
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
                                                       └──Type expr: Variable: a23344
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
                                                    └──Type expr: Variable: a23344
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
                                                       └──Type expr: Variable: a23344
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
                                                       └──Type expr: Variable: a23344
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
                                                             └──Type expr: Variable: a23344
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
                                                          └──Type expr: Variable: a23344
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
                                                                   └──Type expr: Variable: a23344
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
                               └──Type expr: Variable: a23395
                   └──Desc: Variable: b
                └──Abstraction:
                   └──Variables: a23395
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
                                  └──Type expr: Variable: a23395
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
                                           └──Type expr: Variable: a23395
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
                                              └──Type expr: Variable: a23395
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
                                           └──Type expr: Variable: a23395
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
                                        └──Type expr: Variable: a23395
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
                                           └──Type expr: Variable: a23395
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
                                           └──Type expr: Variable: a23395
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
                                                 └──Type expr: Variable: a23395
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
                                              └──Type expr: Variable: a23395
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
                                                       └──Type expr: Variable: a23395
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
                                                          └──Type expr: Variable: a23395
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
                                                       └──Type expr: Variable: a23395
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
                                                    └──Type expr: Variable: a23395
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
                                                       └──Type expr: Variable: a23395
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
                                                       └──Type expr: Variable: a23395
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
                                                             └──Type expr: Variable: a23395
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
                                                          └──Type expr: Variable: a23395
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
                                                                   └──Type expr: Variable: a23395
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
                                  └──Type expr: Variable: a23432
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
                                     └──Type expr: Variable: a23432
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
                                              └──Type expr: Variable: a23432
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
                                              └──Type expr: Variable: a23432
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
                                                    └──Type expr: Variable: a23432
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
                                                       └──Type expr: Variable: a23432
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
                                                       └──Type expr: Variable: a23432
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
                                                 └──Type expr: Variable: a23432
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
                                                 └──Type expr: Variable: a23432
                                  └──Desc: Variable
                                     └──Variable: a
                                     └──Type expr: Row cons
                                        └──Label: Pear
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Variable: a23432
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
                                           └──Type expr: Variable: a23432
                            └──Desc: Variable
                               └──Variable: b
                               └──Type expr: Row cons
                                  └──Label: Orange
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: string
                                  └──Type expr: Variable: a23432 |}]