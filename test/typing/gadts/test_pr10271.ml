open! Import
open Util

let%expect_test "pr10271-1" =
  let str =
    {|
      type 'a t = 
        | Int constraint 'a = int
      ;;

      type packed = 
        | Packed of 'a. 'a t * 'a
      ;;

      let test = 
        let x = Packed (Int, 0) in
        match x with
        ( Packed (Int, v) -> (v : int))
      ;;

      (* second test is the same w/ modules *)

      external ignore : 'a. 'a -> unit = "%ignore";;
      
      let f = fun (Packed (type 'a) ((w, x) : 'a t * 'a)) -> ignore (x : 'a) ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: t
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Int
                   └──Constructor alphas: 40
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 40
                   └──Constraint:
                      └──Type expr: Variable: 40
                      └──Type expr: Constructor: int
       └──Structure item: Type
          └──Type declaration:
             └──Type name: packed
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Packed
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: packed
                   └──Constructor argument:
                      └──Constructor betas: 43
                      └──Type expr: Tuple
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: 43
                         └──Type expr: Variable: 43
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: int
                   └──Desc: Variable: test
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: int
                      └──Desc: Let
                         └──Value bindings:
                            └──Value binding:
                               └──Pattern:
                                  └──Type expr: Constructor: packed
                                  └──Desc: Variable: x
                               └──Abstraction:
                                  └──Variables:
                                  └──Expression:
                                     └──Type expr: Constructor: packed
                                     └──Desc: Construct
                                        └──Constructor description:
                                           └──Name: Packed
                                           └──Constructor argument type:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                           └──Constructor type:
                                              └──Type expr: Constructor: packed
                                        └──Expression:
                                           └──Type expr: Tuple
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Constructor: int
                                              └──Type expr: Constructor: int
                                           └──Desc: Tuple
                                              └──Expression:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Constructor: int
                                                 └──Desc: Construct
                                                    └──Constructor description:
                                                       └──Name: Int
                                                       └──Constructor type:
                                                          └──Type expr: Constructor: t
                                                             └──Type expr: Constructor: int
                                              └──Expression:
                                                 └──Type expr: Constructor: int
                                                 └──Desc: Constant: 0
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: packed
                                  └──Desc: Variable
                                     └──Variable: x
                               └──Type expr: Constructor: packed
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: packed
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Packed
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: t
                                                       └──Type expr: Variable: 27
                                                    └──Type expr: Variable: 27
                                              └──Constructor type:
                                                 └──Type expr: Constructor: packed
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: 27
                                                 └──Type expr: Variable: 27
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: t
                                                       └──Type expr: Variable: 27
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: t
                                                                └──Type expr: Variable: 27
                                                 └──Pattern:
                                                    └──Type expr: Variable: 27
                                                    └──Desc: Variable: v
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Variable
                                           └──Variable: v
       └──Structure item: Primitive
          └──Value description:
             └──Name: ignore
             └──Scheme:
                └──Variables: 45
                └──Type expr: Arrow
                   └──Type expr: Variable: 45
                   └──Type expr: Constructor: unit
             └──Primitive name: %ignore
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: packed
                      └──Type expr: Constructor: unit
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: packed
                         └──Type expr: Constructor: unit
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: packed
                            └──Desc: Construct
                               └──Constructor description:
                                  └──Name: Packed
                                  └──Constructor argument type:
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: 75
                                        └──Type expr: Variable: 75
                                  └──Constructor type:
                                     └──Type expr: Constructor: packed
                               └──Pattern:
                                  └──Type expr: Tuple
                                     └──Type expr: Constructor: t
                                        └──Type expr: Variable: 75
                                     └──Type expr: Variable: 75
                                  └──Desc: Tuple
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: 75
                                        └──Desc: Variable: w
                                     └──Pattern:
                                        └──Type expr: Variable: 75
                                        └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: unit
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 75
                                     └──Type expr: Constructor: unit
                                  └──Desc: Variable
                                     └──Variable: ignore
                                     └──Type expr: Variable: 75
                               └──Expression:
                                  └──Type expr: Variable: 75
                                  └──Desc: Variable
                                     └──Variable: x |}]
