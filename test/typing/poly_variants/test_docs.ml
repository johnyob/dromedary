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
                   └──Constructor alphas: 29308
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 29308
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 29308
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 29308
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: 29308
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 29308
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
                               └──Type expr: Variable: 29358
                   └──Desc: Variable: xs
                └──Abstraction:
                   └──Variables: 29358
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
                                  └──Type expr: Variable: 29358
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
                                           └──Type expr: Variable: 29358
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
                                              └──Type expr: Variable: 29358
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
                                           └──Type expr: Variable: 29358
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
                                        └──Type expr: Variable: 29358
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
                                           └──Type expr: Variable: 29358
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
                                           └──Type expr: Variable: 29358
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
                                                 └──Type expr: Variable: 29358
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
                                              └──Type expr: Variable: 29358
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
                                                       └──Type expr: Variable: 29358
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
                                                          └──Type expr: Variable: 29358
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
                                                       └──Type expr: Variable: 29358
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
                                                    └──Type expr: Variable: 29358
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
                                                       └──Type expr: Variable: 29358
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
                                                       └──Type expr: Variable: 29358
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
                                                             └──Type expr: Variable: 29358
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
                                                          └──Type expr: Variable: 29358
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
                                                                   └──Type expr: Variable: 29358
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Variant
                      └──Type expr: Row cons
                         └──Label: Number
                         └──Type expr: Constructor: present
                            └──Type expr: Constructor: int
                         └──Type expr: Variable: 29366
                   └──Desc: Any
                └──Abstraction:
                   └──Variables: 29366
                   └──Expression:
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Number
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: int
                            └──Type expr: Variable: 29366
                      └──Desc: Variant
                         └──Variant description:
                            └──Tag: Number
                            └──Variant row:
                               └──Type expr: Row cons
                                  └──Label: Number
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: int
                                  └──Type expr: Variable: 29366
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
                └──Variables: 29432,29431
                └──Type expr: Arrow
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: 29431
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: 29431
                         └──Type expr: Variable: 29432
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 29432
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
                                        └──Type expr: Variable: 29540
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: C
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: unit
                            └──Type expr: Row cons
                               └──Label: D
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Variable: 29540
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
                                           └──Type expr: Variable: 29540
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: C
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Row cons
                                  └──Label: D
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Variable: 29540
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
                                              └──Type expr: Variable: 29540
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
                                     └──Type expr: Variable: 29540
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
                                                    └──Type expr: Variable: 29540
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
                                                 └──Type expr: Variable: 29540
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
                                                          └──Type expr: Variable: 29540
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
                                                                └──Type expr: Variable: 29540
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
                                                 └──Type expr: Variable: 29540
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
                                                       └──Type expr: Variable: 29540
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
                                                          └──Type expr: Variable: 29540
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
                                                                └──Type expr: Variable: 29540
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
                                                 └──Type expr: Variable: 29540
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
                                                       └──Type expr: Variable: 29540
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
                                                          └──Type expr: Variable: 29540
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
                                                 └──Type expr: Variable: 29540
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
                      └──Type expr: Variable: 29550
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Int
                            └──Type expr: Constructor: present
                               └──Type expr: Variable: 29550
                            └──Type expr: Variable: 29549
                   └──Desc: Variable: int
                └──Abstraction:
                   └──Variables: 29549,29550,29550
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 29550
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Int
                               └──Type expr: Constructor: present
                                  └──Type expr: Variable: 29550
                               └──Type expr: Variable: 29549
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 29550
                            └──Desc: Variable: n
                         └──Expression:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Int
                                  └──Type expr: Constructor: present
                                     └──Type expr: Variable: 29550
                                  └──Type expr: Variable: 29549
                            └──Desc: Variant
                               └──Variant description:
                                  └──Tag: Int
                                  └──Variant row:
                                     └──Type expr: Row cons
                                        └──Label: Int
                                        └──Type expr: Constructor: present
                                           └──Type expr: Variable: 29550
                                        └──Type expr: Variable: 29549
                               └──Expression:
                                  └──Type expr: Variable: 29550
                                  └──Desc: Variable
                                     └──Variable: n
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 29558
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Num
                               └──Type expr: Constructor: present
                                  └──Type expr: Variable: 29563
                               └──Type expr: Row uniform
                                  └──Type expr: Constructor: absent
                         └──Type expr: Variable: 29563
                   └──Desc: Variable: eval_inner
                └──Abstraction:
                   └──Variables: 29558
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 29558
                         └──Type expr: Arrow
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Num
                                  └──Type expr: Constructor: present
                                     └──Type expr: Variable: 29563
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                            └──Type expr: Variable: 29563
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 29558
                            └──Desc: Variable: eval
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Num
                                     └──Type expr: Constructor: present
                                        └──Type expr: Variable: 29563
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                               └──Type expr: Variable: 29563
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Num
                                        └──Type expr: Constructor: present
                                           └──Type expr: Variable: 29563
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Variable: 29563
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Num
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Variable: 29563
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Num
                                           └──Type expr: Constructor: present
                                              └──Type expr: Variable: 29563
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: 29563
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Desc: Variant
                                                 └──Variant description:
                                                    └──Tag: Num
                                                    └──Variant row:
                                                       └──Type expr: Row cons
                                                          └──Label: Num
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Variable: 29563
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                                 └──Pattern:
                                                    └──Type expr: Variable: 29563
                                                    └──Desc: Variable: n
                                           └──Expression:
                                              └──Type expr: Variable: 29563
                                              └──Desc: Variable
                                                 └──Variable: n
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: eval
                └──Abstraction:
                   └──Variables: 29588
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Num
                               └──Type expr: Constructor: present
                                  └──Type expr: Variable: 29588
                               └──Type expr: Row uniform
                                  └──Type expr: Constructor: absent
                         └──Type expr: Variable: 29588
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Num
                                  └──Type expr: Constructor: present
                                     └──Type expr: Variable: 29588
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Variable: 29588
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Num
                                           └──Type expr: Constructor: present
                                              └──Type expr: Variable: 29588
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                                     └──Type expr: Variable: 29588
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: 29588
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Type expr: Variable: 29588
                                           └──Type expr: Arrow
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: 29588
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Type expr: Variable: 29588
                                        └──Desc: Variable
                                           └──Variable: eval_inner
                                           └──Type expr: Variable: 29588
                                           └──Type expr: Arrow
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: 29588
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Type expr: Variable: 29588
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Num
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Variable: 29588
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                           └──Type expr: Variable: 29588
                                        └──Desc: Variable
                                           └──Variable: eval
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Num
                                        └──Type expr: Constructor: present
                                           └──Type expr: Variable: 29588
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
                      └──Type expr: Variable: 29613
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Int
                            └──Type expr: Constructor: present
                               └──Type expr: Variable: 29613
                            └──Type expr: Variable: 29612
                   └──Desc: Variable: int
                └──Abstraction:
                   └──Variables: 29612,29613,29613
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 29613
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Int
                               └──Type expr: Constructor: present
                                  └──Type expr: Variable: 29613
                               └──Type expr: Variable: 29612
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 29613
                            └──Desc: Variable: n
                         └──Expression:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Int
                                  └──Type expr: Constructor: present
                                     └──Type expr: Variable: 29613
                                  └──Type expr: Variable: 29612
                            └──Desc: Variant
                               └──Variant description:
                                  └──Tag: Int
                                  └──Variant row:
                                     └──Type expr: Row cons
                                        └──Label: Int
                                        └──Type expr: Constructor: present
                                           └──Type expr: Variable: 29613
                                        └──Type expr: Variable: 29612
                               └──Expression:
                                  └──Type expr: Variable: 29613
                                  └──Desc: Variable
                                     └──Variable: n
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 29621
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Num
                               └──Type expr: Constructor: present
                                  └──Type expr: Variable: 29626
                               └──Type expr: Row uniform
                                  └──Type expr: Constructor: absent
                         └──Type expr: Variable: 29626
                   └──Desc: Variable: eval1_inner
                └──Abstraction:
                   └──Variables: 29621
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 29621
                         └──Type expr: Arrow
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Num
                                  └──Type expr: Constructor: present
                                     └──Type expr: Variable: 29626
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                            └──Type expr: Variable: 29626
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 29621
                            └──Desc: Variable: eval
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Num
                                     └──Type expr: Constructor: present
                                        └──Type expr: Variable: 29626
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                               └──Type expr: Variable: 29626
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Num
                                        └──Type expr: Constructor: present
                                           └──Type expr: Variable: 29626
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                                  └──Desc: Variable: e
                               └──Expression:
                                  └──Type expr: Variable: 29626
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Num
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Variable: 29626
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                                        └──Desc: Variable
                                           └──Variable: e
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Num
                                           └──Type expr: Constructor: present
                                              └──Type expr: Variable: 29626
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: 29626
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Desc: Variant
                                                 └──Variant description:
                                                    └──Tag: Num
                                                    └──Variant row:
                                                       └──Type expr: Row cons
                                                          └──Label: Num
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Variable: 29626
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                                 └──Pattern:
                                                    └──Type expr: Variable: 29626
                                                    └──Desc: Variable: n
                                           └──Expression:
                                              └──Type expr: Variable: 29626
                                              └──Desc: Variable
                                                 └──Variable: n
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: eval1
                └──Abstraction:
                   └──Variables: 29651
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Num
                               └──Type expr: Constructor: present
                                  └──Type expr: Variable: 29651
                               └──Type expr: Row uniform
                                  └──Type expr: Constructor: absent
                         └──Type expr: Variable: 29651
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Num
                                  └──Type expr: Constructor: present
                                     └──Type expr: Variable: 29651
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                            └──Desc: Variable: e
                         └──Expression:
                            └──Type expr: Variable: 29651
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Num
                                           └──Type expr: Constructor: present
                                              └──Type expr: Variable: 29651
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                                     └──Type expr: Variable: 29651
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: 29651
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Type expr: Variable: 29651
                                           └──Type expr: Arrow
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: 29651
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Type expr: Variable: 29651
                                        └──Desc: Variable
                                           └──Variable: eval1_inner
                                           └──Type expr: Variable: 29651
                                           └──Type expr: Arrow
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Num
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Variable: 29651
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                              └──Type expr: Variable: 29651
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Num
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Variable: 29651
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                           └──Type expr: Variable: 29651
                                        └──Desc: Variable
                                           └──Variable: eval1
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Num
                                        └──Type expr: Constructor: present
                                           └──Type expr: Variable: 29651
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                                  └──Desc: Variable
                                     └──Variable: e
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 29685
                      └──Type expr: Arrow
                         └──Type expr: Variable: 29686
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Plus
                               └──Type expr: Constructor: present
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: 29685
                                     └──Type expr: Variable: 29686
                               └──Type expr: Variable: 29679
                   └──Desc: Variable: plus
                └──Abstraction:
                   └──Variables: 29685,29685
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 29685
                         └──Type expr: Arrow
                            └──Type expr: Variable: 29686
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Plus
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: 29685
                                        └──Type expr: Variable: 29686
                                  └──Type expr: Variable: 29679
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 29685
                            └──Desc: Variable: e1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: 29686
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Plus
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 29685
                                           └──Type expr: Variable: 29686
                                     └──Type expr: Variable: 29679
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: 29686
                                  └──Desc: Variable: e2
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Plus
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 29685
                                              └──Type expr: Variable: 29686
                                        └──Type expr: Variable: 29679
                                  └──Desc: Variant
                                     └──Variant description:
                                        └──Tag: Plus
                                        └──Variant row:
                                           └──Type expr: Row cons
                                              └──Label: Plus
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 29685
                                                    └──Type expr: Variable: 29686
                                              └──Type expr: Variable: 29679
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 29685
                                           └──Type expr: Variable: 29686
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Variable: 29685
                                              └──Desc: Variable
                                                 └──Variable: e1
                                           └──Expression:
                                              └──Type expr: Variable: 29686
                                              └──Desc: Variable
                                                 └──Variable: e2
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: 29739
                         └──Type expr: Constructor: int
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Plus
                               └──Type expr: Constructor: present
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: 29739
                                     └──Type expr: Variable: 29739
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
                   └──Variables: 29739,29739,29739,29739
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: 29739
                            └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Plus
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: 29739
                                        └──Type expr: Variable: 29739
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
                               └──Type expr: Variable: 29739
                               └──Type expr: Constructor: int
                            └──Desc: Variable: eval
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Plus
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 29739
                                           └──Type expr: Variable: 29739
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
                                              └──Type expr: Variable: 29739
                                              └──Type expr: Variable: 29739
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
                                                    └──Type expr: Variable: 29739
                                                    └──Type expr: Variable: 29739
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
                                                 └──Type expr: Variable: 29739
                                                 └──Type expr: Variable: 29739
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
                                                          └──Type expr: Variable: 29739
                                                          └──Type expr: Variable: 29739
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
                                                                └──Type expr: Variable: 29739
                                                                └──Type expr: Variable: 29739
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Num
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: int
                                                                └──Type expr: Row uniform
                                                                   └──Type expr: Constructor: absent
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 29739
                                                       └──Type expr: Variable: 29739
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Variable: 29739
                                                          └──Desc: Variable: e1
                                                       └──Pattern:
                                                          └──Type expr: Variable: 29739
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
                                                                   └──Type expr: Variable: 29739
                                                                   └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: eval
                                                             └──Expression:
                                                                └──Type expr: Variable: 29739
                                                                └──Desc: Variable
                                                                   └──Variable: e1
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: 29739
                                                             └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: eval
                                                       └──Expression:
                                                          └──Type expr: Variable: 29739
                                                          └──Desc: Variable
                                                             └──Variable: e2
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Plus
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 29739
                                                          └──Type expr: Variable: 29739
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
                                                                └──Type expr: Variable: 29739
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
                                                                └──Type expr: Variable: 29739
                                                                └──Type expr: Constructor: int
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: 29739
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
                            └──Variable: 29762
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Plus
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: 29762
                                        └──Type expr: Variable: 29762
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
                               └──Variable: 29762
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Plus
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 29762
                                           └──Type expr: Variable: 29762
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
                                        └──Variable: 29762
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Plus
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 29762
                                                    └──Type expr: Variable: 29762
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
                                                 └──Variable: 29762
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Plus
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 29762
                                                             └──Type expr: Variable: 29762
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
                                                 └──Variable: 29762
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Plus
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 29762
                                                             └──Type expr: Variable: 29762
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
                                              └──Variable: 29762
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Plus
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 29762
                                                          └──Type expr: Variable: 29762
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
                                              └──Variable: 29762
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Plus
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 29762
                                                          └──Type expr: Variable: 29762
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
                                     └──Variable: 29762
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Plus
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: 29762
                                                 └──Type expr: Variable: 29762
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Num
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: int
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                  └──Desc: Variable
                                     └──Variable: e |}]