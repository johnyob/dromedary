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
                               └──Type expr: Variable: a16132
                   └──Desc: Variable: xs
                └──Abstraction:
                   └──Variables: a16132
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
                                  └──Type expr: Variable: a16132
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
                                           └──Type expr: Variable: a16132
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
                                              └──Type expr: Variable: a16132
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
                                           └──Type expr: Variable: a16132
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
                                        └──Type expr: Variable: a16132
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
                                           └──Type expr: Variable: a16132
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
                                           └──Type expr: Variable: a16132
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
                                                 └──Type expr: Variable: a16132
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
                                              └──Type expr: Variable: a16132
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
                                                       └──Type expr: Variable: a16132
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
                                                          └──Type expr: Variable: a16132
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
                                                       └──Type expr: Variable: a16132
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
                                                    └──Type expr: Variable: a16132
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
                                                       └──Type expr: Variable: a16132
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
                                                       └──Type expr: Variable: a16132
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
                                                             └──Type expr: Variable: a16132
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
                                                          └──Type expr: Variable: a16132
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
                                                                   └──Type expr: Variable: a16132
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Variant
                      └──Type expr: Row cons
                         └──Label: Number
                         └──Type expr: Constructor: present
                            └──Type expr: Constructor: int
                         └──Type expr: Variable: a16140
                   └──Desc: Any
                └──Abstraction:
                   └──Variables: a16140
                   └──Expression:
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Number
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: int
                            └──Type expr: Variable: a16140
                      └──Desc: Variant
                         └──Variant description:
                            └──Tag: Number
                            └──Variant row:
                               └──Type expr: Row cons
                                  └──Label: Number
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: int
                                  └──Type expr: Variable: a16140
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
                └──Variables: a16206,a16205
                └──Type expr: Arrow
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: a16205
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: a16205
                         └──Type expr: Variable: a16206
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a16206
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
                                        └──Type expr: Variable: a16314
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: C
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: unit
                            └──Type expr: Row cons
                               └──Label: D
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Variable: a16314
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
                                           └──Type expr: Variable: a16314
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: C
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Row cons
                                  └──Label: D
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Variable: a16314
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
                                              └──Type expr: Variable: a16314
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
                                     └──Type expr: Variable: a16314
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
                                                    └──Type expr: Variable: a16314
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
                                                 └──Type expr: Variable: a16314
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
                                                          └──Type expr: Variable: a16314
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
                                                                └──Type expr: Variable: a16314
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
                                                 └──Type expr: Variable: a16314
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
                                                       └──Type expr: Variable: a16314
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
                                                          └──Type expr: Variable: a16314
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
                                                                └──Type expr: Variable: a16314
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
                                                 └──Type expr: Variable: a16314
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
                                                       └──Type expr: Variable: a16314
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
                                                          └──Type expr: Variable: a16314
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
                                                 └──Type expr: Variable: a16314
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
                      └──Type expr: Variable: a16324
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Int
                            └──Type expr: Constructor: present
                               └──Type expr: Variable: a16324
                            └──Type expr: Variable: a16323
                   └──Desc: Variable: int
                └──Abstraction:
                   └──Variables: a16323,a16324,a16324
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a16324
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Int
                               └──Type expr: Constructor: present
                                  └──Type expr: Variable: a16324
                               └──Type expr: Variable: a16323
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a16324
                            └──Desc: Variable: n
                         └──Expression:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Int
                                  └──Type expr: Constructor: present
                                     └──Type expr: Variable: a16324
                                  └──Type expr: Variable: a16323
                            └──Desc: Variant
                               └──Variant description:
                                  └──Tag: Int
                                  └──Variant row:
                                     └──Type expr: Row cons
                                        └──Label: Int
                                        └──Type expr: Constructor: present
                                           └──Type expr: Variable: a16324
                                        └──Type expr: Variable: a16323
                               └──Expression:
                                  └──Type expr: Variable: a16324
                                  └──Desc: Variable
                                     └──Variable: n
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: a16332
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Num
                               └──Type expr: Constructor: present
                                  └──Type expr: Variable: a16337
                               └──Type expr: Row uniform
                                  └──Type expr: Constructor: absent
                         └──Type expr: Variable: a16337
                   └──Desc: Variable: eval_inner
                └──Abstraction:
                   └──Variables: a16332
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a16332
                         └──Type expr: Arrow
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Num
                                  └──Type expr: Constructor: present
                                     └──Type expr: Variable: a16337
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                            └──Type expr: Variable: a16337
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a16332
                            └──Desc: Variable: eval
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Num
                                     └──Type expr: Constructor: present
                                        └──Type expr: Variable: a16337
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                               └──Type expr: Variable: a16337
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Num
                                        └──Type expr: Constructor: present
                                           └──Type expr: Variable: a16337
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Variable: a16337
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Num
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Variable: a16337
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Num
                                           └──Type expr: Constructor: present
                                              └──Type expr: Variable: a16337
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: a16337
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Desc: Variant
                                                 └──Variant description:
                                                    └──Tag: Num
                                                    └──Variant row:
                                                       └──Type expr: Row cons
                                                          └──Label: Num
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Variable: a16337
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                                 └──Pattern:
                                                    └──Type expr: Variable: a16337
                                                    └──Desc: Variable: n
                                           └──Expression:
                                              └──Type expr: Variable: a16337
                                              └──Desc: Variable
                                                 └──Variable: n
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: eval
                └──Abstraction:
                   └──Variables: a16362
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Num
                               └──Type expr: Constructor: present
                                  └──Type expr: Variable: a16362
                               └──Type expr: Row uniform
                                  └──Type expr: Constructor: absent
                         └──Type expr: Variable: a16362
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Num
                                  └──Type expr: Constructor: present
                                     └──Type expr: Variable: a16362
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Variable: a16362
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Num
                                           └──Type expr: Constructor: present
                                              └──Type expr: Variable: a16362
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                                     └──Type expr: Variable: a16362
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: a16362
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Type expr: Variable: a16362
                                           └──Type expr: Arrow
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: a16362
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Type expr: Variable: a16362
                                        └──Desc: Variable
                                           └──Variable: eval_inner
                                           └──Type expr: Variable: a16362
                                           └──Type expr: Arrow
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: a16362
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Type expr: Variable: a16362
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Num
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Variable: a16362
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                           └──Type expr: Variable: a16362
                                        └──Desc: Variable
                                           └──Variable: eval
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Num
                                        └──Type expr: Constructor: present
                                           └──Type expr: Variable: a16362
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
                      └──Type expr: Variable: a16387
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Int
                            └──Type expr: Constructor: present
                               └──Type expr: Variable: a16387
                            └──Type expr: Variable: a16386
                   └──Desc: Variable: int
                └──Abstraction:
                   └──Variables: a16386,a16387,a16387
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a16387
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Int
                               └──Type expr: Constructor: present
                                  └──Type expr: Variable: a16387
                               └──Type expr: Variable: a16386
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a16387
                            └──Desc: Variable: n
                         └──Expression:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Int
                                  └──Type expr: Constructor: present
                                     └──Type expr: Variable: a16387
                                  └──Type expr: Variable: a16386
                            └──Desc: Variant
                               └──Variant description:
                                  └──Tag: Int
                                  └──Variant row:
                                     └──Type expr: Row cons
                                        └──Label: Int
                                        └──Type expr: Constructor: present
                                           └──Type expr: Variable: a16387
                                        └──Type expr: Variable: a16386
                               └──Expression:
                                  └──Type expr: Variable: a16387
                                  └──Desc: Variable
                                     └──Variable: n
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: a16395
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Num
                               └──Type expr: Constructor: present
                                  └──Type expr: Variable: a16400
                               └──Type expr: Row uniform
                                  └──Type expr: Constructor: absent
                         └──Type expr: Variable: a16400
                   └──Desc: Variable: eval1_inner
                └──Abstraction:
                   └──Variables: a16395
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a16395
                         └──Type expr: Arrow
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Num
                                  └──Type expr: Constructor: present
                                     └──Type expr: Variable: a16400
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                            └──Type expr: Variable: a16400
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a16395
                            └──Desc: Variable: eval
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Num
                                     └──Type expr: Constructor: present
                                        └──Type expr: Variable: a16400
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                               └──Type expr: Variable: a16400
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Num
                                        └──Type expr: Constructor: present
                                           └──Type expr: Variable: a16400
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                                  └──Desc: Variable: e
                               └──Expression:
                                  └──Type expr: Variable: a16400
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Num
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Variable: a16400
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                                        └──Desc: Variable
                                           └──Variable: e
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Num
                                           └──Type expr: Constructor: present
                                              └──Type expr: Variable: a16400
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: a16400
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Desc: Variant
                                                 └──Variant description:
                                                    └──Tag: Num
                                                    └──Variant row:
                                                       └──Type expr: Row cons
                                                          └──Label: Num
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Variable: a16400
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                                 └──Pattern:
                                                    └──Type expr: Variable: a16400
                                                    └──Desc: Variable: n
                                           └──Expression:
                                              └──Type expr: Variable: a16400
                                              └──Desc: Variable
                                                 └──Variable: n
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: eval1
                └──Abstraction:
                   └──Variables: a16425
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Num
                               └──Type expr: Constructor: present
                                  └──Type expr: Variable: a16425
                               └──Type expr: Row uniform
                                  └──Type expr: Constructor: absent
                         └──Type expr: Variable: a16425
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Num
                                  └──Type expr: Constructor: present
                                     └──Type expr: Variable: a16425
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                            └──Desc: Variable: e
                         └──Expression:
                            └──Type expr: Variable: a16425
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Num
                                           └──Type expr: Constructor: present
                                              └──Type expr: Variable: a16425
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                                     └──Type expr: Variable: a16425
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: a16425
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Type expr: Variable: a16425
                                           └──Type expr: Arrow
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: a16425
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Type expr: Variable: a16425
                                        └──Desc: Variable
                                           └──Variable: eval1_inner
                                           └──Type expr: Variable: a16425
                                           └──Type expr: Arrow
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: a16425
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Type expr: Variable: a16425
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Num
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Variable: a16425
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                           └──Type expr: Variable: a16425
                                        └──Desc: Variable
                                           └──Variable: eval1
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Num
                                        └──Type expr: Constructor: present
                                           └──Type expr: Variable: a16425
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                                  └──Desc: Variable
                                     └──Variable: e
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: a16459
                      └──Type expr: Arrow
                         └──Type expr: Variable: a16460
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Plus
                               └──Type expr: Constructor: present
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: a16459
                                     └──Type expr: Variable: a16460
                               └──Type expr: Variable: a16453
                   └──Desc: Variable: plus
                └──Abstraction:
                   └──Variables: a16459,a16459
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a16459
                         └──Type expr: Arrow
                            └──Type expr: Variable: a16460
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Plus
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: a16459
                                        └──Type expr: Variable: a16460
                                  └──Type expr: Variable: a16453
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a16459
                            └──Desc: Variable: e1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a16460
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Plus
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a16459
                                           └──Type expr: Variable: a16460
                                     └──Type expr: Variable: a16453
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: a16460
                                  └──Desc: Variable: e2
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Plus
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a16459
                                              └──Type expr: Variable: a16460
                                        └──Type expr: Variable: a16453
                                  └──Desc: Variant
                                     └──Variant description:
                                        └──Tag: Plus
                                        └──Variant row:
                                           └──Type expr: Row cons
                                              └──Label: Plus
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a16459
                                                    └──Type expr: Variable: a16460
                                              └──Type expr: Variable: a16453
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a16459
                                           └──Type expr: Variable: a16460
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Variable: a16459
                                              └──Desc: Variable
                                                 └──Variable: e1
                                           └──Expression:
                                              └──Type expr: Variable: a16460
                                              └──Desc: Variable
                                                 └──Variable: e2
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: a16513
                         └──Type expr: Constructor: int
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Plus
                               └──Type expr: Constructor: present
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: a16513
                                     └──Type expr: Variable: a16513
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
                   └──Variables: a16513,a16513,a16513,a16513
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: a16513
                            └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Plus
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: a16513
                                        └──Type expr: Variable: a16513
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
                               └──Type expr: Variable: a16513
                               └──Type expr: Constructor: int
                            └──Desc: Variable: eval
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Plus
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a16513
                                           └──Type expr: Variable: a16513
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
                                              └──Type expr: Variable: a16513
                                              └──Type expr: Variable: a16513
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
                                                    └──Type expr: Variable: a16513
                                                    └──Type expr: Variable: a16513
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
                                                 └──Type expr: Variable: a16513
                                                 └──Type expr: Variable: a16513
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
                                                          └──Type expr: Variable: a16513
                                                          └──Type expr: Variable: a16513
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
                                                                └──Type expr: Variable: a16513
                                                                └──Type expr: Variable: a16513
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Num
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: int
                                                                └──Type expr: Row uniform
                                                                   └──Type expr: Constructor: absent
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a16513
                                                       └──Type expr: Variable: a16513
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Variable: a16513
                                                          └──Desc: Variable: e1
                                                       └──Pattern:
                                                          └──Type expr: Variable: a16513
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
                                                                   └──Type expr: Variable: a16513
                                                                   └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: eval
                                                             └──Expression:
                                                                └──Type expr: Variable: a16513
                                                                └──Desc: Variable
                                                                   └──Variable: e1
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a16513
                                                             └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: eval
                                                       └──Expression:
                                                          └──Type expr: Variable: a16513
                                                          └──Desc: Variable
                                                             └──Variable: e2
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Plus
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a16513
                                                          └──Type expr: Variable: a16513
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
                                                                └──Type expr: Variable: a16513
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
                                                                └──Type expr: Variable: a16513
                                                                └──Type expr: Constructor: int
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a16513
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
                            └──Variable: a16536
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Plus
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: a16536
                                        └──Type expr: Variable: a16536
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
                               └──Variable: a16536
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Plus
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a16536
                                           └──Type expr: Variable: a16536
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
                                        └──Variable: a16536
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Plus
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a16536
                                                    └──Type expr: Variable: a16536
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
                                                 └──Variable: a16536
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Plus
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a16536
                                                             └──Type expr: Variable: a16536
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
                                                 └──Variable: a16536
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Plus
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a16536
                                                             └──Type expr: Variable: a16536
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
                                              └──Variable: a16536
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Plus
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a16536
                                                          └──Type expr: Variable: a16536
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
                                              └──Variable: a16536
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Plus
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a16536
                                                          └──Type expr: Variable: a16536
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
                                     └──Variable: a16536
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Plus
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a16536
                                                 └──Type expr: Variable: a16536
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Num
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: int
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                  └──Desc: Variable
                                     └──Variable: e |}]