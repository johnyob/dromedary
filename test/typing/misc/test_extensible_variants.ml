open! Import
open Util


let%expect_test "" =
  let str = 
    {|
      type 'a eff = ..;;

      type 'a eff += 
        | Yield constraint 'a = unit
        | Fork of unit -> unit constraint 'a = unit
      ;;

      external perform : 'a. 'a eff -> 'a = "%perform";;

      let fork = fun f -> perform (Fork f);;

      let yield = fun () -> perform Yield;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: eff
             └──Type declaration kind: Open
       └──Structure item: Type Extension
          └──Type extension:
             └──Extension name: eff
             └──Extension constructor:
                └──Extension name: eff
                └──Extension parameters: 28358
                └──Extension constructor kind: Declaration
                   └──Constructor declaration:
                      └──Constructor name: Yield
                      └──Constructor alphas: 28358
                      └──Constructor type:
                         └──Type expr: Constructor: eff
                            └──Type expr: Variable: 28358
                      └──Constraint:
                         └──Type expr: Variable: 28358
                         └──Type expr: Constructor: unit
             └──Extension constructor:
                └──Extension name: eff
                └──Extension parameters: 28358
                └──Extension constructor kind: Declaration
                   └──Constructor declaration:
                      └──Constructor name: Fork
                      └──Constructor alphas: 28358
                      └──Constructor type:
                         └──Type expr: Constructor: eff
                            └──Type expr: Variable: 28358
                      └──Constructor argument:
                         └──Constructor betas:
                         └──Type expr: Arrow
                            └──Type expr: Constructor: unit
                            └──Type expr: Constructor: unit
                      └──Constraint:
                         └──Type expr: Variable: 28358
                         └──Type expr: Constructor: unit
       └──Structure item: Primitive
          └──Value description:
             └──Name: perform
             └──Scheme:
                └──Variables: 28366
                └──Type expr: Arrow
                   └──Type expr: Constructor: eff
                      └──Type expr: Variable: 28366
                   └──Type expr: Variable: 28366
             └──Primitive name: %perform
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Constructor: unit
                         └──Type expr: Constructor: unit
                      └──Type expr: Constructor: unit
                   └──Desc: Variable: fork
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Constructor: unit
                            └──Type expr: Constructor: unit
                         └──Type expr: Constructor: unit
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: unit
                               └──Type expr: Constructor: unit
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Constructor: unit
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: eff
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Constructor: unit
                                  └──Desc: Variable
                                     └──Variable: perform
                                     └──Type expr: Constructor: unit
                               └──Expression:
                                  └──Type expr: Constructor: eff
                                     └──Type expr: Constructor: unit
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Fork
                                        └──Constructor argument type:
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: unit
                                              └──Type expr: Constructor: unit
                                        └──Constructor type:
                                           └──Type expr: Constructor: eff
                                              └──Type expr: Constructor: unit
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: unit
                                           └──Type expr: Constructor: unit
                                        └──Desc: Variable
                                           └──Variable: f
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: unit
                      └──Type expr: Constructor: unit
                   └──Desc: Variable: yield
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: unit
                         └──Type expr: Constructor: unit
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: unit
                            └──Desc: Constant: ()
                         └──Expression:
                            └──Type expr: Constructor: unit
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: eff
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Constructor: unit
                                  └──Desc: Variable
                                     └──Variable: perform
                                     └──Type expr: Constructor: unit
                               └──Expression:
                                  └──Type expr: Constructor: eff
                                     └──Type expr: Constructor: unit
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Yield
                                        └──Constructor type:
                                           └──Type expr: Constructor: eff
                                              └──Type expr: Constructor: unit |}]