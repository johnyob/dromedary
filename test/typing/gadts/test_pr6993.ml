open! Import
open Util

let%expect_test "" = 
  let str = 
    {|
      type ('a, 'b) cmp = 
        | Eq constraint 'a = 'b
        | Not_eq of string
      ;;

      external print_endline : string -> unit = "%print_endline";;

      let (type 'a) f = 
        fun (t : ('a list, 'a) cmp) ->
          match t with 
          ( Eq -> ()
          | Not_eq s -> print_endline s
          )
      ;;

      (* We support recursive aliases :) *)
      type b_t = b_t list;;
      let eq = (Eq : (b_t list, b_t) cmp);;

      let _ = 
        f eq;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: cmp
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Eq
                   └──Constructor alphas: 42 43
                   └──Constructor type:
                      └──Type expr: Constructor: cmp
                         └──Type expr: Variable: 42
                         └──Type expr: Variable: 43
                   └──Constraint:
                      └──Type expr: Variable: 42
                      └──Type expr: Variable: 43
                └──Constructor declaration:
                   └──Constructor name: Not_eq
                   └──Constructor alphas: 42 43
                   └──Constructor type:
                      └──Type expr: Constructor: cmp
                         └──Type expr: Variable: 42
                         └──Type expr: Variable: 43
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: string
       └──Structure item: Primitive
          └──Value description:
             └──Name: print_endline
             └──Scheme:
                └──Variables:
                └──Type expr: Arrow
                   └──Type expr: Constructor: string
                   └──Type expr: Constructor: unit
             └──Primitive name: %print_endline
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: cmp
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 21
                         └──Type expr: Variable: 21
                      └──Type expr: Constructor: unit
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: 21
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: cmp
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: 21
                            └──Type expr: Variable: 21
                         └──Type expr: Constructor: unit
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: cmp
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: 21
                               └──Type expr: Variable: 21
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: unit
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: cmp
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: 21
                                     └──Type expr: Variable: 21
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: cmp
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: 21
                                  └──Type expr: Variable: 21
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: cmp
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: 21
                                           └──Type expr: Variable: 21
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Eq
                                              └──Constructor type:
                                                 └──Type expr: Constructor: cmp
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: 21
                                                    └──Type expr: Variable: 21
                                     └──Expression:
                                        └──Type expr: Constructor: unit
                                        └──Desc: Constant: ()
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: cmp
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: 21
                                           └──Type expr: Variable: 21
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Not_eq
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: string
                                              └──Constructor type:
                                                 └──Type expr: Constructor: cmp
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: 21
                                                    └──Type expr: Variable: 21
                                           └──Pattern:
                                              └──Type expr: Constructor: string
                                              └──Desc: Variable: s
                                     └──Expression:
                                        └──Type expr: Constructor: unit
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: string
                                                 └──Type expr: Constructor: unit
                                              └──Desc: Variable
                                                 └──Variable: print_endline
                                           └──Expression:
                                              └──Type expr: Constructor: string
                                              └──Desc: Variable
                                                 └──Variable: s
       └──Structure item: Type
          └──Type declaration:
             └──Type name: b_t
             └──Type declaration kind: Alias
                └──Alias
                   └──Alias name: b_t
                   └──Alias alphas:
                   └──Type expr: Constructor: list
                      └──Type expr: Constructor: b_t
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: cmp
                      └──Type expr: Constructor: list
                         └──Type expr: Constructor: b_t
                      └──Type expr: Constructor: b_t
                   └──Desc: Variable: eq
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: cmp
                         └──Type expr: Constructor: list
                            └──Type expr: Constructor: b_t
                         └──Type expr: Constructor: b_t
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: Eq
                            └──Constructor type:
                               └──Type expr: Constructor: cmp
                                  └──Type expr: Constructor: list
                                     └──Type expr: Constructor: b_t
                                  └──Type expr: Constructor: list
                                     └──Type expr: Constructor: b_t
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: unit
                   └──Desc: Any
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: unit
                      └──Desc: Application
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: cmp
                                  └──Type expr: Constructor: list
                                     └──Type expr: Constructor: b_t
                                  └──Type expr: Constructor: b_t
                               └──Type expr: Constructor: unit
                            └──Desc: Variable
                               └──Variable: f
                               └──Type expr: Constructor: b_t
                         └──Expression:
                            └──Type expr: Constructor: cmp
                               └──Type expr: Constructor: list
                                  └──Type expr: Constructor: b_t
                               └──Type expr: Constructor: b_t
                            └──Desc: Variable
                               └──Variable: eq |}]