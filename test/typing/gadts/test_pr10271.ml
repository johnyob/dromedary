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
  [%expect{|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: t
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Int
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
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
                      └──Constructor betas: a
                      └──Type expr: Tuple
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: a
                         └──Type expr: Variable: a
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
                                                       └──Type expr: Variable: a7402
                                                    └──Type expr: Variable: a7402
                                              └──Constructor type:
                                                 └──Type expr: Constructor: packed
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: a7402
                                                 └──Type expr: Variable: a7402
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: t
                                                       └──Type expr: Variable: a7402
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: t
                                                                └──Type expr: Variable: a7402
                                                 └──Pattern:
                                                    └──Type expr: Variable: a7402
                                                    └──Desc: Variable: v
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Variable
                                           └──Variable: v
       └──Structure item: Primitive
          └──Value description:
             └──Name: ignore
             └──Scheme:
                └──Variables: a7420
                └──Type expr: Arrow
                   └──Type expr: Variable: a7420
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
                                           └──Type expr: Variable: a7450
                                        └──Type expr: Variable: a7450
                                  └──Constructor type:
                                     └──Type expr: Constructor: packed
                               └──Pattern:
                                  └──Type expr: Tuple
                                     └──Type expr: Constructor: t
                                        └──Type expr: Variable: a7450
                                     └──Type expr: Variable: a7450
                                  └──Desc: Tuple
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: a7450
                                        └──Desc: Variable: w
                                     └──Pattern:
                                        └──Type expr: Variable: a7450
                                        └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: unit
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a7450
                                     └──Type expr: Constructor: unit
                                  └──Desc: Variable
                                     └──Variable: ignore
                                     └──Type expr: Variable: a7450
                               └──Expression:
                                  └──Type expr: Variable: a7450
                                  └──Desc: Variable
                                     └──Variable: x |}]