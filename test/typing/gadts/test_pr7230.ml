open! Import
open Util

let%expect_test "" = 
  let str = 
    {|
      type 'a t = 
        | Int constraint 'a = int
      ;;

      external raise : 'a. exn -> 'a = "%raise";;
      exception Not_found;;
      exception Assert_false;;

      let _ = 
        match (raise Not_found : float t) with ( _ -> raise Assert_false )
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
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
       └──Structure item: Primitive
          └──Value description:
             └──Name: raise
             └──Scheme:
                └──Variables: a5860
                └──Type expr: Arrow
                   └──Type expr: Constructor: exn
                   └──Type expr: Variable: a5860
             └──Primitive name: %raise
       └──Structure item: Exception
          └──Type exception:
             └──Extension constructor:
                └──Extension name: exn
                └──Extension parameters:
                └──Extension constructor kind: Declaration
                   └──Constructor declaration:
                      └──Constructor name: Not_found
                      └──Constructor alphas:
                      └──Constructor type:
                         └──Type expr: Constructor: exn
       └──Structure item: Exception
          └──Type exception:
             └──Extension constructor:
                └──Extension name: exn
                └──Extension parameters:
                └──Extension constructor kind: Declaration
                   └──Constructor declaration:
                      └──Constructor name: Assert_false
                      └──Constructor alphas:
                      └──Constructor type:
                         └──Type expr: Constructor: exn
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Variable: a5865
                   └──Desc: Any
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Variable: a5865
                      └──Desc: Match
                         └──Expression:
                            └──Type expr: Constructor: t
                               └──Type expr: Constructor: float
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: exn
                                     └──Type expr: Constructor: t
                                        └──Type expr: Constructor: float
                                  └──Desc: Variable
                                     └──Variable: raise
                                     └──Type expr: Constructor: t
                                        └──Type expr: Constructor: float
                               └──Expression:
                                  └──Type expr: Constructor: exn
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Not_found
                                        └──Constructor type:
                                           └──Type expr: Constructor: exn
                         └──Type expr: Constructor: t
                            └──Type expr: Constructor: float
                         └──Cases:
                            └──Case:
                               └──Pattern:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Constructor: float
                                  └──Desc: Any
                               └──Expression:
                                  └──Type expr: Variable: a5865
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: exn
                                           └──Type expr: Variable: a5865
                                        └──Desc: Variable
                                           └──Variable: raise
                                           └──Type expr: Variable: a5865
                                     └──Expression:
                                        └──Type expr: Constructor: exn
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Assert_false
                                              └──Constructor type:
                                                 └──Type expr: Constructor: exn |}]