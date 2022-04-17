open! Import
open Util

let%expect_test "" = 
  let str = 
    {|
      type 'a visit_action;; 
      type insert;;
      type 'a local_visit_action;;

      type ('a, 'result, 'visit_action) context = 
        | Local of 'insert. unit constraint 'result = 'a * 'insert and 'visit_action = 'a local_visit_action
        | Global constraint 'a = 'result and 'visit_action = 'a visit_action
      ;;

      external raise : 'a. exn -> 'a = "%raise";;

      exception Exit;;

      let (type 'visit_action) vexpr = 
        exists (type 'a 'result 'c) ->
          fun (ctx : ('a, 'result, 'visit_action) context) ->
            (match ctx with 
             ( Local () -> fun _ -> raise Exit
             | Global -> fun _ -> raise Exit
             )
            : 'c -> 'visit_action)
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    "Non rigid equations" |}]

let%expect_test "" = 
  let str = 
    {|
      type 'a visit_action;; 
      type insert;;
      type 'a local_visit_action;;

      type ('a, 'result, 'visit_action) context = 
        | Local of 'insert. unit constraint 'result = 'a * 'insert and 'visit_action = 'a local_visit_action
        | Global constraint 'a = 'result and 'visit_action = 'a visit_action
      ;;

      external raise : 'a. exn -> 'a = "%raise";;

      exception Exit;;

      let (type 'result 'visit_action) vexpr = 
        fun (ctx : (unit, 'result, 'visit_action) context) ->
          (match ctx with
           ( Local () -> fun _ -> raise Exit
           | Global -> fun _ -> raise Exit
           ) 
          : unit -> 'visit_action)
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: visit_action
             └──Type declaration kind: Abstract
       └──Structure item: Type
          └──Type declaration:
             └──Type name: insert
             └──Type declaration kind: Abstract
       └──Structure item: Type
          └──Type declaration:
             └──Type name: local_visit_action
             └──Type declaration kind: Abstract
       └──Structure item: Type
          └──Type declaration:
             └──Type name: context
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Local
                   └──Constructor alphas: 16059 16060 16061
                   └──Constructor type:
                      └──Type expr: Constructor: context
                         └──Type expr: Variable: 16059
                         └──Type expr: Variable: 16060
                         └──Type expr: Variable: 16061
                   └──Constructor argument:
                      └──Constructor betas: 16062
                      └──Type expr: Constructor: unit
                   └──Constraint:
                      └──Type expr: Variable: 16060
                      └──Type expr: Tuple
                         └──Type expr: Variable: 16059
                         └──Type expr: Variable: 16062
                   └──Constraint:
                      └──Type expr: Variable: 16061
                      └──Type expr: Constructor: local_visit_action
                         └──Type expr: Variable: 16059
                └──Constructor declaration:
                   └──Constructor name: Global
                   └──Constructor alphas: 16059 16060 16061
                   └──Constructor type:
                      └──Type expr: Constructor: context
                         └──Type expr: Variable: 16059
                         └──Type expr: Variable: 16060
                         └──Type expr: Variable: 16061
                   └──Constraint:
                      └──Type expr: Variable: 16059
                      └──Type expr: Variable: 16060
                   └──Constraint:
                      └──Type expr: Variable: 16061
                      └──Type expr: Constructor: visit_action
                         └──Type expr: Variable: 16059
       └──Structure item: Primitive
          └──Value description:
             └──Name: raise
             └──Scheme:
                └──Variables: 16070
                └──Type expr: Arrow
                   └──Type expr: Constructor: exn
                   └──Type expr: Variable: 16070
             └──Primitive name: %raise
       └──Structure item: Exception
          └──Type exception:
             └──Extension constructor:
                └──Extension name: exn
                └──Extension parameters:
                └──Extension constructor kind: Declaration
                   └──Constructor declaration:
                      └──Constructor name: Exit
                      └──Constructor alphas:
                      └──Constructor type:
                         └──Type expr: Constructor: exn
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: context
                         └──Type expr: Constructor: unit
                         └──Type expr: Variable: 16088
                         └──Type expr: Variable: 16089
                      └──Type expr: Arrow
                         └──Type expr: Constructor: unit
                         └──Type expr: Variable: 16089
                   └──Desc: Variable: vexpr
                └──Abstraction:
                   └──Variables: 16088,16089
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: context
                            └──Type expr: Constructor: unit
                            └──Type expr: Variable: 16088
                            └──Type expr: Variable: 16089
                         └──Type expr: Arrow
                            └──Type expr: Constructor: unit
                            └──Type expr: Variable: 16089
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: context
                               └──Type expr: Constructor: unit
                               └──Type expr: Variable: 16088
                               └──Type expr: Variable: 16089
                            └──Desc: Variable: ctx
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: unit
                               └──Type expr: Variable: 16089
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: context
                                     └──Type expr: Constructor: unit
                                     └──Type expr: Variable: 16088
                                     └──Type expr: Variable: 16089
                                  └──Desc: Variable
                                     └──Variable: ctx
                               └──Type expr: Constructor: context
                                  └──Type expr: Constructor: unit
                                  └──Type expr: Variable: 16088
                                  └──Type expr: Variable: 16089
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: context
                                           └──Type expr: Constructor: unit
                                           └──Type expr: Variable: 16088
                                           └──Type expr: Variable: 16089
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Local
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: context
                                                    └──Type expr: Constructor: unit
                                                    └──Type expr: Variable: 16088
                                                    └──Type expr: Variable: 16089
                                           └──Pattern:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Constant: ()
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: unit
                                           └──Type expr: Variable: 16089
                                        └──Desc: Function
                                           └──Pattern:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Any
                                           └──Expression:
                                              └──Type expr: Variable: 16089
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: exn
                                                       └──Type expr: Variable: 16089
                                                    └──Desc: Variable
                                                       └──Variable: raise
                                                       └──Type expr: Variable: 16089
                                                 └──Expression:
                                                    └──Type expr: Constructor: exn
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Exit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: exn
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: context
                                           └──Type expr: Constructor: unit
                                           └──Type expr: Variable: 16088
                                           └──Type expr: Variable: 16089
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Global
                                              └──Constructor type:
                                                 └──Type expr: Constructor: context
                                                    └──Type expr: Constructor: unit
                                                    └──Type expr: Variable: 16088
                                                    └──Type expr: Variable: 16089
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: unit
                                           └──Type expr: Variable: 16089
                                        └──Desc: Function
                                           └──Pattern:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Any
                                           └──Expression:
                                              └──Type expr: Variable: 16089
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: exn
                                                       └──Type expr: Variable: 16089
                                                    └──Desc: Variable
                                                       └──Variable: raise
                                                       └──Type expr: Variable: 16089
                                                 └──Expression:
                                                    └──Type expr: Constructor: exn
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Exit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: exn |}]