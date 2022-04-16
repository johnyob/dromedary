open! Import
open Util

(* Examples from https://ocaml.org/manual/polyvariant.html *)

let%expect_test "" =
  let str = 
    {|
      type 'a list = 
        | Nil
        | Cons of 'a * 'a list
      ;;

      let xs = Cons (`On, Cons (`Off, Nil));;

      let _ = `Number 1;;

      let f = 
        fun t ->
          match t with
          ( `On -> 1
          | `Off -> 0 
          | `Number n -> n
          )
      ;;

      external map : 'a 'b. 'a list -> ('a -> 'b) -> 'b list = "%map";;

      let _ = map xs f;; 
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
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: list
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Off
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: unit
                            └──Type expr: Row cons
                               └──Label: On
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Variable: a27770
                   └──Desc: Variable: xs
                └──Abstraction:
                   └──Variables: a27770
                   └──Expression:
                      └──Type expr: Constructor: list
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Off
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Row cons
                                  └──Label: On
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Variable: a27770
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: Cons
                            └──Constructor argument type:
                               └──Type expr: Tuple
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Off
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: On
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: a27770
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Off
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row cons
                                              └──Label: On
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Variable: a27770
                            └──Constructor type:
                               └──Type expr: Constructor: list
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Off
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: On
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: a27770
                         └──Expression:
                            └──Type expr: Tuple
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Off
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row cons
                                        └──Label: On
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Variable: a27770
                               └──Type expr: Constructor: list
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Off
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: On
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: a27770
                            └──Desc: Tuple
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Off
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: On
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: a27770
                                  └──Desc: Variant
                                     └──Variant description:
                                        └──Tag: On
                                        └──Variant row:
                                           └──Type expr: Row cons
                                              └──Label: Off
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: On
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Variable: a27770
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Off
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row cons
                                              └──Label: On
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Variable: a27770
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Cons
                                        └──Constructor argument type:
                                           └──Type expr: Tuple
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Off
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: On
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Variable: a27770
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Off
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: On
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Variable: a27770
                                        └──Constructor type:
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Off
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: On
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Variable: a27770
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Off
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: On
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Variable: a27770
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Off
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: On
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Variable: a27770
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Off
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: On
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Variable: a27770
                                              └──Desc: Variant
                                                 └──Variant description:
                                                    └──Tag: Off
                                                    └──Variant row:
                                                       └──Type expr: Row cons
                                                          └──Label: Off
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: On
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: a27770
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Off
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: On
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Variable: a27770
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Off
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: On
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: a27770
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Variant
                      └──Type expr: Row cons
                         └──Label: Number
                         └──Type expr: Constructor: present
                            └──Type expr: Constructor: int
                         └──Type expr: Variable: a27778
                   └──Desc: Any
                └──Abstraction:
                   └──Variables: a27778
                   └──Expression:
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Number
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: int
                            └──Type expr: Variable: a27778
                      └──Desc: Variant
                         └──Variant description:
                            └──Tag: Number
                            └──Variant row:
                               └──Type expr: Row cons
                                  └──Label: Number
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: int
                                  └──Type expr: Variable: a27778
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Constant: 1
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: On
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: unit
                            └──Type expr: Row cons
                               └──Label: Off
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Row cons
                                  └──Label: Number
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: int
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                      └──Type expr: Constructor: int
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: On
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Row cons
                                  └──Label: Off
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Row cons
                                     └──Label: Number
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: int
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: On
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Row cons
                                     └──Label: Off
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row cons
                                        └──Label: Number
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: int
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: On
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: Off
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row cons
                                              └──Label: Number
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: int
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: On
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row cons
                                        └──Label: Off
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: Number
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: int
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: On
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Off
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Number
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: On
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: On
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Off
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Number
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: int
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 1
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: On
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Off
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Number
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Off
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: On
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Off
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Number
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: int
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 0
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: On
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Off
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Number
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Number
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: On
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Off
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Number
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: int
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                           └──Pattern:
                                              └──Type expr: Constructor: int
                                              └──Desc: Variable: n
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Variable
                                           └──Variable: n
       └──Structure item: Primitive
          └──Value description:
             └──Name: map
             └──Scheme:
                └──Variables: a27844,a27843
                └──Type expr: Arrow
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: a27843
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: a27843
                         └──Type expr: Variable: a27844
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a27844
             └──Primitive name: %map
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: list
                      └──Type expr: Constructor: int
                   └──Desc: Any
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: list
                         └──Type expr: Constructor: int
                      └──Desc: Application
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Off
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: On
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row cons
                                              └──Label: Number
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: int
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                                  └──Type expr: Constructor: int
                               └──Type expr: Constructor: list
                                  └──Type expr: Constructor: int
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Off
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: On
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Number
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                     └──Type expr: Arrow
                                        └──Type expr: Arrow
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Off
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: On
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Number
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: int
                                                       └──Type expr: Row uniform
                                                          └──Type expr: Constructor: absent
                                           └──Type expr: Constructor: int
                                        └──Type expr: Constructor: list
                                           └──Type expr: Constructor: int
                                  └──Desc: Variable
                                     └──Variable: map
                                     └──Type expr: Constructor: int
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Off
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row cons
                                              └──Label: On
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Number
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: int
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Off
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row cons
                                              └──Label: On
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Number
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: int
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                  └──Desc: Variable
                                     └──Variable: xs
                                     └──Type expr: Row cons
                                        └──Label: Number
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: int
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Off
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row cons
                                        └──Label: On
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: Number
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: int
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                               └──Type expr: Constructor: int
                            └──Desc: Variable
                               └──Variable: f |}]

let%expect_test "" =
  let str = 
    {|
      (* Semantically different to OCaml, since we handle 
         default cases differently *)
      let f = 
        fun t -> 
          match t with
          ( `A -> `C
          | `B -> `D 
          | x -> x
          )
      ;;
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
                   └──Type expr: Arrow
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: A
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: unit
                            └──Type expr: Row cons
                               └──Label: B
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: C
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row cons
                                        └──Label: D
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Variable: a27952
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: C
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: unit
                            └──Type expr: Row cons
                               └──Label: D
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Variable: a27952
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: A
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Row cons
                                  └──Label: B
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: C
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: D
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: a27952
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: C
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Row cons
                                  └──Label: D
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Variable: a27952
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: A
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Row cons
                                     └──Label: B
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: C
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row cons
                                              └──Label: D
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Variable: a27952
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: C
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Row cons
                                     └──Label: D
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Variable: a27952
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: A
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: B
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: C
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: D
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Variable: a27952
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: A
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row cons
                                        └──Label: B
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: C
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: D
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Variable: a27952
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: A
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: B
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: C
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: D
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Variable: a27952
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: A
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: A
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: B
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: C
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: D
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a27952
                                     └──Expression:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: C
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: D
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Variable: a27952
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: C
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: C
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: D
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Variable: a27952
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: A
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: B
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: C
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: D
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Variable: a27952
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: B
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: A
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: B
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: C
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: D
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a27952
                                     └──Expression:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: C
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: D
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Variable: a27952
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: D
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: C
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: D
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Variable: a27952
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: A
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: B
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: C
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: D
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Variable: a27952
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: C
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: D
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Variable: a27952
                                        └──Desc: Variable
                                           └──Variable: x |}]

let%expect_test "" =
  let str = 
    {|
      let int = fun n -> `Int n;;
      
      let eval_inner = fun eval t ->
        match t with (`Num n -> n)
      ;;

      let rec eval = fun t -> eval_inner eval t;;
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
                   └──Type expr: Arrow
                      └──Type expr: Variable: a27962
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Int
                            └──Type expr: Constructor: present
                               └──Type expr: Variable: a27962
                            └──Type expr: Variable: a27961
                   └──Desc: Variable: int
                └──Abstraction:
                   └──Variables: a27961,a27962,a27962
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a27962
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Int
                               └──Type expr: Constructor: present
                                  └──Type expr: Variable: a27962
                               └──Type expr: Variable: a27961
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a27962
                            └──Desc: Variable: n
                         └──Expression:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Int
                                  └──Type expr: Constructor: present
                                     └──Type expr: Variable: a27962
                                  └──Type expr: Variable: a27961
                            └──Desc: Variant
                               └──Variant description:
                                  └──Tag: Int
                                  └──Variant row:
                                     └──Type expr: Row cons
                                        └──Label: Int
                                        └──Type expr: Constructor: present
                                           └──Type expr: Variable: a27962
                                        └──Type expr: Variable: a27961
                               └──Expression:
                                  └──Type expr: Variable: a27962
                                  └──Desc: Variable
                                     └──Variable: n
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: a27970
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Num
                               └──Type expr: Constructor: present
                                  └──Type expr: Variable: a27975
                               └──Type expr: Row uniform
                                  └──Type expr: Constructor: absent
                         └──Type expr: Variable: a27975
                   └──Desc: Variable: eval_inner
                └──Abstraction:
                   └──Variables: a27970
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a27970
                         └──Type expr: Arrow
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Num
                                  └──Type expr: Constructor: present
                                     └──Type expr: Variable: a27975
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                            └──Type expr: Variable: a27975
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a27970
                            └──Desc: Variable: eval
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Num
                                     └──Type expr: Constructor: present
                                        └──Type expr: Variable: a27975
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                               └──Type expr: Variable: a27975
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Num
                                        └──Type expr: Constructor: present
                                           └──Type expr: Variable: a27975
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Variable: a27975
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Num
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Variable: a27975
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Num
                                           └──Type expr: Constructor: present
                                              └──Type expr: Variable: a27975
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: a27975
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Desc: Variant
                                                 └──Variant description:
                                                    └──Tag: Num
                                                    └──Variant row:
                                                       └──Type expr: Row cons
                                                          └──Label: Num
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Variable: a27975
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                                 └──Pattern:
                                                    └──Type expr: Variable: a27975
                                                    └──Desc: Variable: n
                                           └──Expression:
                                              └──Type expr: Variable: a27975
                                              └──Desc: Variable
                                                 └──Variable: n
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: eval
                └──Abstraction:
                   └──Variables: a28000
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Num
                               └──Type expr: Constructor: present
                                  └──Type expr: Variable: a28000
                               └──Type expr: Row uniform
                                  └──Type expr: Constructor: absent
                         └──Type expr: Variable: a28000
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Num
                                  └──Type expr: Constructor: present
                                     └──Type expr: Variable: a28000
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Variable: a28000
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Num
                                           └──Type expr: Constructor: present
                                              └──Type expr: Variable: a28000
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                                     └──Type expr: Variable: a28000
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: a28000
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Type expr: Variable: a28000
                                           └──Type expr: Arrow
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: a28000
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Type expr: Variable: a28000
                                        └──Desc: Variable
                                           └──Variable: eval_inner
                                           └──Type expr: Variable: a28000
                                           └──Type expr: Arrow
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: a28000
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Type expr: Variable: a28000
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Num
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Variable: a28000
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                           └──Type expr: Variable: a28000
                                        └──Desc: Variable
                                           └──Variable: eval
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Num
                                        └──Type expr: Constructor: present
                                           └──Type expr: Variable: a28000
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                                  └──Desc: Variable
                                     └──Variable: t |}]

let%expect_test "" =
  let str = 
    {|
      let int = fun n -> `Int n;;
        
      let eval1_inner = fun eval e ->
        match e with (`Num n -> n)
      ;;

      let rec eval1 = fun e -> eval1_inner eval1 e;;

      let plus = fun e1 e2 -> `Plus (e1, e2);;

      let eval2_inner = fun eval e ->
        match e with
        ( `Plus (e1, e2) -> eval e1 + eval e2
        | e -> eval1_inner eval e 
        )
      ;;

      let rec eval2 = fun e -> eval2_inner eval2 e;;
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
                   └──Type expr: Arrow
                      └──Type expr: Variable: a28025
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Int
                            └──Type expr: Constructor: present
                               └──Type expr: Variable: a28025
                            └──Type expr: Variable: a28024
                   └──Desc: Variable: int
                └──Abstraction:
                   └──Variables: a28024,a28025,a28025
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a28025
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Int
                               └──Type expr: Constructor: present
                                  └──Type expr: Variable: a28025
                               └──Type expr: Variable: a28024
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a28025
                            └──Desc: Variable: n
                         └──Expression:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Int
                                  └──Type expr: Constructor: present
                                     └──Type expr: Variable: a28025
                                  └──Type expr: Variable: a28024
                            └──Desc: Variant
                               └──Variant description:
                                  └──Tag: Int
                                  └──Variant row:
                                     └──Type expr: Row cons
                                        └──Label: Int
                                        └──Type expr: Constructor: present
                                           └──Type expr: Variable: a28025
                                        └──Type expr: Variable: a28024
                               └──Expression:
                                  └──Type expr: Variable: a28025
                                  └──Desc: Variable
                                     └──Variable: n
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: a28033
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Num
                               └──Type expr: Constructor: present
                                  └──Type expr: Variable: a28038
                               └──Type expr: Row uniform
                                  └──Type expr: Constructor: absent
                         └──Type expr: Variable: a28038
                   └──Desc: Variable: eval1_inner
                └──Abstraction:
                   └──Variables: a28033
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a28033
                         └──Type expr: Arrow
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Num
                                  └──Type expr: Constructor: present
                                     └──Type expr: Variable: a28038
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                            └──Type expr: Variable: a28038
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a28033
                            └──Desc: Variable: eval
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Num
                                     └──Type expr: Constructor: present
                                        └──Type expr: Variable: a28038
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                               └──Type expr: Variable: a28038
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Num
                                        └──Type expr: Constructor: present
                                           └──Type expr: Variable: a28038
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                                  └──Desc: Variable: e
                               └──Expression:
                                  └──Type expr: Variable: a28038
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Num
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Variable: a28038
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                                        └──Desc: Variable
                                           └──Variable: e
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Num
                                           └──Type expr: Constructor: present
                                              └──Type expr: Variable: a28038
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: a28038
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Desc: Variant
                                                 └──Variant description:
                                                    └──Tag: Num
                                                    └──Variant row:
                                                       └──Type expr: Row cons
                                                          └──Label: Num
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Variable: a28038
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                                 └──Pattern:
                                                    └──Type expr: Variable: a28038
                                                    └──Desc: Variable: n
                                           └──Expression:
                                              └──Type expr: Variable: a28038
                                              └──Desc: Variable
                                                 └──Variable: n
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: eval1
                └──Abstraction:
                   └──Variables: a28063
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Num
                               └──Type expr: Constructor: present
                                  └──Type expr: Variable: a28063
                               └──Type expr: Row uniform
                                  └──Type expr: Constructor: absent
                         └──Type expr: Variable: a28063
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Num
                                  └──Type expr: Constructor: present
                                     └──Type expr: Variable: a28063
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                            └──Desc: Variable: e
                         └──Expression:
                            └──Type expr: Variable: a28063
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Num
                                           └──Type expr: Constructor: present
                                              └──Type expr: Variable: a28063
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                                     └──Type expr: Variable: a28063
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: a28063
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Type expr: Variable: a28063
                                           └──Type expr: Arrow
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: a28063
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Type expr: Variable: a28063
                                        └──Desc: Variable
                                           └──Variable: eval1_inner
                                           └──Type expr: Variable: a28063
                                           └──Type expr: Arrow
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: a28063
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Type expr: Variable: a28063
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Num
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Variable: a28063
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                           └──Type expr: Variable: a28063
                                        └──Desc: Variable
                                           └──Variable: eval1
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Num
                                        └──Type expr: Constructor: present
                                           └──Type expr: Variable: a28063
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                                  └──Desc: Variable
                                     └──Variable: e
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: a28097
                      └──Type expr: Arrow
                         └──Type expr: Variable: a28098
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Plus
                               └──Type expr: Constructor: present
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: a28097
                                     └──Type expr: Variable: a28098
                               └──Type expr: Variable: a28091
                   └──Desc: Variable: plus
                └──Abstraction:
                   └──Variables: a28097,a28097
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a28097
                         └──Type expr: Arrow
                            └──Type expr: Variable: a28098
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Plus
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: a28097
                                        └──Type expr: Variable: a28098
                                  └──Type expr: Variable: a28091
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a28097
                            └──Desc: Variable: e1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a28098
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Plus
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a28097
                                           └──Type expr: Variable: a28098
                                     └──Type expr: Variable: a28091
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: a28098
                                  └──Desc: Variable: e2
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Plus
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a28097
                                              └──Type expr: Variable: a28098
                                        └──Type expr: Variable: a28091
                                  └──Desc: Variant
                                     └──Variant description:
                                        └──Tag: Plus
                                        └──Variant row:
                                           └──Type expr: Row cons
                                              └──Label: Plus
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a28097
                                                    └──Type expr: Variable: a28098
                                              └──Type expr: Variable: a28091
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a28097
                                           └──Type expr: Variable: a28098
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Variable: a28097
                                              └──Desc: Variable
                                                 └──Variable: e1
                                           └──Expression:
                                              └──Type expr: Variable: a28098
                                              └──Desc: Variable
                                                 └──Variable: e2
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: a28151
                         └──Type expr: Constructor: int
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Plus
                               └──Type expr: Constructor: present
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: a28151
                                     └──Type expr: Variable: a28151
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Num
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: int
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                         └──Type expr: Constructor: int
                   └──Desc: Variable: eval2_inner
                └──Abstraction:
                   └──Variables: a28151,a28151,a28151,a28151
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: a28151
                            └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Plus
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: a28151
                                        └──Type expr: Variable: a28151
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Num
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: int
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                            └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a28151
                               └──Type expr: Constructor: int
                            └──Desc: Variable: eval
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Plus
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a28151
                                           └──Type expr: Variable: a28151
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Num
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: int
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                               └──Type expr: Constructor: int
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Plus
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a28151
                                              └──Type expr: Variable: a28151
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Num
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: int
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                                  └──Desc: Variable: e
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Plus
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a28151
                                                    └──Type expr: Variable: a28151
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                        └──Desc: Variable
                                           └──Variable: e
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Plus
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a28151
                                                 └──Type expr: Variable: a28151
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Num
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: int
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Plus
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a28151
                                                          └──Type expr: Variable: a28151
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Num
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: int
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                              └──Desc: Variant
                                                 └──Variant description:
                                                    └──Tag: Plus
                                                    └──Variant row:
                                                       └──Type expr: Row cons
                                                          └──Label: Plus
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a28151
                                                                └──Type expr: Variable: a28151
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Num
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: int
                                                                └──Type expr: Row uniform
                                                                   └──Type expr: Constructor: absent
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a28151
                                                       └──Type expr: Variable: a28151
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Variable: a28151
                                                          └──Desc: Variable: e1
                                                       └──Pattern:
                                                          └──Type expr: Variable: a28151
                                                          └──Desc: Variable: e2
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
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: a28151
                                                                   └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: eval
                                                             └──Expression:
                                                                └──Type expr: Variable: a28151
                                                                └──Desc: Variable
                                                                   └──Variable: e1
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a28151
                                                             └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: eval
                                                       └──Expression:
                                                          └──Type expr: Variable: a28151
                                                          └──Desc: Variable
                                                             └──Variable: e2
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Plus
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a28151
                                                          └──Type expr: Variable: a28151
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Num
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: int
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                              └──Desc: Variable: e
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Num
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: int
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a28151
                                                                └──Type expr: Constructor: int
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Num
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: int
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                                └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: eval1_inner
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a28151
                                                                └──Type expr: Constructor: int
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a28151
                                                             └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: eval
                                                 └──Expression:
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Num
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: int
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                                    └──Desc: Variable
                                                       └──Variable: e
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: eval2
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Mu
                            └──Variable: a28174
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Plus
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: a28174
                                        └──Type expr: Variable: a28174
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Num
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: int
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Mu
                               └──Variable: a28174
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Plus
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a28174
                                           └──Type expr: Variable: a28174
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Num
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: int
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                            └──Desc: Variable: e
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Mu
                                        └──Variable: a28174
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Plus
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a28174
                                                    └──Type expr: Variable: a28174
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                     └──Type expr: Constructor: int
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Mu
                                                 └──Variable: a28174
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Plus
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a28174
                                                             └──Type expr: Variable: a28174
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Num
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: int
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                              └──Type expr: Constructor: int
                                           └──Type expr: Arrow
                                              └──Type expr: Mu
                                                 └──Variable: a28174
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Plus
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a28174
                                                             └──Type expr: Variable: a28174
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Num
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: int
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                              └──Type expr: Constructor: int
                                        └──Desc: Variable
                                           └──Variable: eval2_inner
                                           └──Type expr: Mu
                                              └──Variable: a28174
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Plus
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a28174
                                                          └──Type expr: Variable: a28174
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Num
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: int
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Mu
                                              └──Variable: a28174
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Plus
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a28174
                                                          └──Type expr: Variable: a28174
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Num
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: int
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                           └──Type expr: Constructor: int
                                        └──Desc: Variable
                                           └──Variable: eval2
                               └──Expression:
                                  └──Type expr: Mu
                                     └──Variable: a28174
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Plus
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a28174
                                                 └──Type expr: Variable: a28174
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Num
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: int
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                  └──Desc: Variable
                                     └──Variable: e |}]