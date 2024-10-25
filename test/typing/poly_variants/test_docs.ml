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
                   └──Constructor alphas: 826
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 826
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 826
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 826
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: 826
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 826
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
                               └──Type expr: Variable: 45
                   └──Desc: Variable: xs
                └──Abstraction:
                   └──Variables: 45
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
                                  └──Type expr: Variable: 45
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
                                           └──Type expr: Variable: 45
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
                                              └──Type expr: Variable: 45
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
                                           └──Type expr: Variable: 45
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
                                        └──Type expr: Variable: 45
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
                                           └──Type expr: Variable: 45
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
                                           └──Type expr: Variable: 45
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
                                                 └──Type expr: Variable: 45
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
                                              └──Type expr: Variable: 45
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
                                                       └──Type expr: Variable: 45
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
                                                          └──Type expr: Variable: 45
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
                                                       └──Type expr: Variable: 45
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
                                                    └──Type expr: Variable: 45
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
                                                       └──Type expr: Variable: 45
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
                                                       └──Type expr: Variable: 45
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
                                                             └──Type expr: Variable: 45
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
                                                          └──Type expr: Variable: 45
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
                                                                   └──Type expr: Variable: 45
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Variant
                      └──Type expr: Row cons
                         └──Label: Number
                         └──Type expr: Constructor: present
                            └──Type expr: Constructor: int
                         └──Type expr: Variable: 53
                   └──Desc: Any
                └──Abstraction:
                   └──Variables: 53
                   └──Expression:
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Number
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: int
                            └──Type expr: Variable: 53
                      └──Desc: Variant
                         └──Variant description:
                            └──Tag: Number
                            └──Variant row:
                               └──Type expr: Row cons
                                  └──Label: Number
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: int
                                  └──Type expr: Variable: 53
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
                └──Variables: 119,118
                └──Type expr: Arrow
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: 118
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: 118
                         └──Type expr: Variable: 119
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 119
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
  [%expect
    {|
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
                                        └──Type expr: Variable: 58
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: C
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: unit
                            └──Type expr: Row cons
                               └──Label: D
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Variable: 58
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
                                           └──Type expr: Variable: 58
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: C
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Row cons
                                  └──Label: D
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Variable: 58
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
                                              └──Type expr: Variable: 58
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
                                     └──Type expr: Variable: 58
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
                                                    └──Type expr: Variable: 58
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
                                                 └──Type expr: Variable: 58
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
                                                          └──Type expr: Variable: 58
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
                                                                └──Type expr: Variable: 58
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
                                                 └──Type expr: Variable: 58
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
                                                       └──Type expr: Variable: 58
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
                                                          └──Type expr: Variable: 58
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
                                                                └──Type expr: Variable: 58
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
                                                 └──Type expr: Variable: 58
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
                                                       └──Type expr: Variable: 58
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
                                                          └──Type expr: Variable: 58
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
                                                 └──Type expr: Variable: 58
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
  [%expect
    {|
    Structure:
    └──Structure:
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 7
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Int
                            └──Type expr: Constructor: present
                               └──Type expr: Variable: 7
                            └──Type expr: Variable: 6
                   └──Desc: Variable: int
                └──Abstraction:
                   └──Variables: 6,7,7
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 7
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Int
                               └──Type expr: Constructor: present
                                  └──Type expr: Variable: 7
                               └──Type expr: Variable: 6
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 7
                            └──Desc: Variable: n
                         └──Expression:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Int
                                  └──Type expr: Constructor: present
                                     └──Type expr: Variable: 7
                                  └──Type expr: Variable: 6
                            └──Desc: Variant
                               └──Variant description:
                                  └──Tag: Int
                                  └──Variant row:
                                     └──Type expr: Row cons
                                        └──Label: Int
                                        └──Type expr: Constructor: present
                                           └──Type expr: Variable: 7
                                        └──Type expr: Variable: 6
                               └──Expression:
                                  └──Type expr: Variable: 7
                                  └──Desc: Variable
                                     └──Variable: n
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 15
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Num
                               └──Type expr: Constructor: present
                                  └──Type expr: Variable: 20
                               └──Type expr: Row uniform
                                  └──Type expr: Constructor: absent
                         └──Type expr: Variable: 20
                   └──Desc: Variable: eval_inner
                └──Abstraction:
                   └──Variables: 15
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 15
                         └──Type expr: Arrow
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Num
                                  └──Type expr: Constructor: present
                                     └──Type expr: Variable: 20
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                            └──Type expr: Variable: 20
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 15
                            └──Desc: Variable: eval
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Num
                                     └──Type expr: Constructor: present
                                        └──Type expr: Variable: 20
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                               └──Type expr: Variable: 20
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Num
                                        └──Type expr: Constructor: present
                                           └──Type expr: Variable: 20
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Variable: 20
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Num
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Variable: 20
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Num
                                           └──Type expr: Constructor: present
                                              └──Type expr: Variable: 20
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: 20
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Desc: Variant
                                                 └──Variant description:
                                                    └──Tag: Num
                                                    └──Variant row:
                                                       └──Type expr: Row cons
                                                          └──Label: Num
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Variable: 20
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                                 └──Pattern:
                                                    └──Type expr: Variable: 20
                                                    └──Desc: Variable: n
                                           └──Expression:
                                              └──Type expr: Variable: 20
                                              └──Desc: Variable
                                                 └──Variable: n
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: eval
                └──Abstraction:
                   └──Variables: 45
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Num
                               └──Type expr: Constructor: present
                                  └──Type expr: Variable: 45
                               └──Type expr: Row uniform
                                  └──Type expr: Constructor: absent
                         └──Type expr: Variable: 45
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Num
                                  └──Type expr: Constructor: present
                                     └──Type expr: Variable: 45
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Variable: 45
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Num
                                           └──Type expr: Constructor: present
                                              └──Type expr: Variable: 45
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                                     └──Type expr: Variable: 45
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: 45
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Type expr: Variable: 45
                                           └──Type expr: Arrow
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: 45
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Type expr: Variable: 45
                                        └──Desc: Variable
                                           └──Variable: eval_inner
                                           └──Type expr: Variable: 45
                                           └──Type expr: Arrow
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: 45
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Type expr: Variable: 45
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Num
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Variable: 45
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                           └──Type expr: Variable: 45
                                        └──Desc: Variable
                                           └──Variable: eval
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Num
                                        └──Type expr: Constructor: present
                                           └──Type expr: Variable: 45
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
  [%expect
    {|
    Structure:
    └──Structure:
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 7
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Int
                            └──Type expr: Constructor: present
                               └──Type expr: Variable: 7
                            └──Type expr: Variable: 6
                   └──Desc: Variable: int
                └──Abstraction:
                   └──Variables: 6,7,7
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 7
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Int
                               └──Type expr: Constructor: present
                                  └──Type expr: Variable: 7
                               └──Type expr: Variable: 6
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 7
                            └──Desc: Variable: n
                         └──Expression:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Int
                                  └──Type expr: Constructor: present
                                     └──Type expr: Variable: 7
                                  └──Type expr: Variable: 6
                            └──Desc: Variant
                               └──Variant description:
                                  └──Tag: Int
                                  └──Variant row:
                                     └──Type expr: Row cons
                                        └──Label: Int
                                        └──Type expr: Constructor: present
                                           └──Type expr: Variable: 7
                                        └──Type expr: Variable: 6
                               └──Expression:
                                  └──Type expr: Variable: 7
                                  └──Desc: Variable
                                     └──Variable: n
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 15
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Num
                               └──Type expr: Constructor: present
                                  └──Type expr: Variable: 20
                               └──Type expr: Row uniform
                                  └──Type expr: Constructor: absent
                         └──Type expr: Variable: 20
                   └──Desc: Variable: eval1_inner
                └──Abstraction:
                   └──Variables: 15
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 15
                         └──Type expr: Arrow
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Num
                                  └──Type expr: Constructor: present
                                     └──Type expr: Variable: 20
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                            └──Type expr: Variable: 20
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 15
                            └──Desc: Variable: eval
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Num
                                     └──Type expr: Constructor: present
                                        └──Type expr: Variable: 20
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                               └──Type expr: Variable: 20
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Num
                                        └──Type expr: Constructor: present
                                           └──Type expr: Variable: 20
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                                  └──Desc: Variable: e
                               └──Expression:
                                  └──Type expr: Variable: 20
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Num
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Variable: 20
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                                        └──Desc: Variable
                                           └──Variable: e
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Num
                                           └──Type expr: Constructor: present
                                              └──Type expr: Variable: 20
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: 20
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Desc: Variant
                                                 └──Variant description:
                                                    └──Tag: Num
                                                    └──Variant row:
                                                       └──Type expr: Row cons
                                                          └──Label: Num
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Variable: 20
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                                 └──Pattern:
                                                    └──Type expr: Variable: 20
                                                    └──Desc: Variable: n
                                           └──Expression:
                                              └──Type expr: Variable: 20
                                              └──Desc: Variable
                                                 └──Variable: n
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: eval1
                └──Abstraction:
                   └──Variables: 45
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Num
                               └──Type expr: Constructor: present
                                  └──Type expr: Variable: 45
                               └──Type expr: Row uniform
                                  └──Type expr: Constructor: absent
                         └──Type expr: Variable: 45
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Num
                                  └──Type expr: Constructor: present
                                     └──Type expr: Variable: 45
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                            └──Desc: Variable: e
                         └──Expression:
                            └──Type expr: Variable: 45
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Num
                                           └──Type expr: Constructor: present
                                              └──Type expr: Variable: 45
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                                     └──Type expr: Variable: 45
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: 45
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Type expr: Variable: 45
                                           └──Type expr: Arrow
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: 45
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Type expr: Variable: 45
                                        └──Desc: Variable
                                           └──Variable: eval1_inner
                                           └──Type expr: Variable: 45
                                           └──Type expr: Arrow
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: 45
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Type expr: Variable: 45
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Num
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Variable: 45
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                           └──Type expr: Variable: 45
                                        └──Desc: Variable
                                           └──Variable: eval1
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Num
                                        └──Type expr: Constructor: present
                                           └──Type expr: Variable: 45
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                                  └──Desc: Variable
                                     └──Variable: e
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 79
                      └──Type expr: Arrow
                         └──Type expr: Variable: 80
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Plus
                               └──Type expr: Constructor: present
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: 79
                                     └──Type expr: Variable: 80
                               └──Type expr: Variable: 73
                   └──Desc: Variable: plus
                └──Abstraction:
                   └──Variables: 79,79
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 79
                         └──Type expr: Arrow
                            └──Type expr: Variable: 80
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Plus
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: 79
                                        └──Type expr: Variable: 80
                                  └──Type expr: Variable: 73
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 79
                            └──Desc: Variable: e1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: 80
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Plus
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 79
                                           └──Type expr: Variable: 80
                                     └──Type expr: Variable: 73
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: 80
                                  └──Desc: Variable: e2
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Plus
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 79
                                              └──Type expr: Variable: 80
                                        └──Type expr: Variable: 73
                                  └──Desc: Variant
                                     └──Variant description:
                                        └──Tag: Plus
                                        └──Variant row:
                                           └──Type expr: Row cons
                                              └──Label: Plus
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 79
                                                    └──Type expr: Variable: 80
                                              └──Type expr: Variable: 73
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 79
                                           └──Type expr: Variable: 80
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Variable: 79
                                              └──Desc: Variable
                                                 └──Variable: e1
                                           └──Expression:
                                              └──Type expr: Variable: 80
                                              └──Desc: Variable
                                                 └──Variable: e2
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: 133
                         └──Type expr: Constructor: int
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Plus
                               └──Type expr: Constructor: present
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: 133
                                     └──Type expr: Variable: 133
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
                   └──Variables: 133,133,133,133
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: 133
                            └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Plus
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: 133
                                        └──Type expr: Variable: 133
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
                               └──Type expr: Variable: 133
                               └──Type expr: Constructor: int
                            └──Desc: Variable: eval
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Plus
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 133
                                           └──Type expr: Variable: 133
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
                                              └──Type expr: Variable: 133
                                              └──Type expr: Variable: 133
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
                                                    └──Type expr: Variable: 133
                                                    └──Type expr: Variable: 133
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
                                                 └──Type expr: Variable: 133
                                                 └──Type expr: Variable: 133
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
                                                          └──Type expr: Variable: 133
                                                          └──Type expr: Variable: 133
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
                                                                └──Type expr: Variable: 133
                                                                └──Type expr: Variable: 133
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Num
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: int
                                                                └──Type expr: Row uniform
                                                                   └──Type expr: Constructor: absent
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 133
                                                       └──Type expr: Variable: 133
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Variable: 133
                                                          └──Desc: Variable: e1
                                                       └──Pattern:
                                                          └──Type expr: Variable: 133
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
                                                                   └──Type expr: Variable: 133
                                                                   └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: eval
                                                             └──Expression:
                                                                └──Type expr: Variable: 133
                                                                └──Desc: Variable
                                                                   └──Variable: e1
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: 133
                                                             └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: eval
                                                       └──Expression:
                                                          └──Type expr: Variable: 133
                                                          └──Desc: Variable
                                                             └──Variable: e2
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Plus
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 133
                                                          └──Type expr: Variable: 133
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
                                                                └──Type expr: Variable: 133
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
                                                                └──Type expr: Variable: 133
                                                                └──Type expr: Constructor: int
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: 133
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
                            └──Variable: 156
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Plus
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: 156
                                        └──Type expr: Variable: 156
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
                               └──Variable: 156
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Plus
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 156
                                           └──Type expr: Variable: 156
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
                                        └──Variable: 156
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Plus
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 156
                                                    └──Type expr: Variable: 156
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
                                                 └──Variable: 156
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Plus
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 156
                                                             └──Type expr: Variable: 156
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
                                                 └──Variable: 156
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Plus
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 156
                                                             └──Type expr: Variable: 156
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
                                              └──Variable: 156
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Plus
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 156
                                                          └──Type expr: Variable: 156
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
                                              └──Variable: 156
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Plus
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 156
                                                          └──Type expr: Variable: 156
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
                                     └──Variable: 156
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Plus
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: 156
                                                 └──Type expr: Variable: 156
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Num
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: int
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                  └──Desc: Variable
                                     └──Variable: e |}]
