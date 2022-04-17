open! Import
open Util

let%expect_test "" = 
  let str = 
    {|
      type ('a, 'b) segment = 
        | Seg_nil constraint 'a = 'b
        | Seg_cons of ('a * 'a, 'b) segment 
      ;;

      let (type 'a 'b) color = 
        fun (seg : ('a, 'b) segment) ->
          match seg with
          ( Seg_nil -> 0
          | Seg_cons Seg_nil -> 0
          | Seg_cons _ -> 0
          )
      ;; 
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: segment
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Seg_nil
                   └──Constructor alphas: 14987 14988
                   └──Constructor type:
                      └──Type expr: Constructor: segment
                         └──Type expr: Variable: 14987
                         └──Type expr: Variable: 14988
                   └──Constraint:
                      └──Type expr: Variable: 14987
                      └──Type expr: Variable: 14988
                └──Constructor declaration:
                   └──Constructor name: Seg_cons
                   └──Constructor alphas: 14987 14988
                   └──Constructor type:
                      └──Type expr: Constructor: segment
                         └──Type expr: Variable: 14987
                         └──Type expr: Variable: 14988
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: segment
                         └──Type expr: Tuple
                            └──Type expr: Variable: 14987
                            └──Type expr: Variable: 14987
                         └──Type expr: Variable: 14988
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: segment
                         └──Type expr: Variable: 15003
                         └──Type expr: Variable: 15004
                      └──Type expr: Constructor: int
                   └──Desc: Variable: color
                └──Abstraction:
                   └──Variables: 15003,15004
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: segment
                            └──Type expr: Variable: 15003
                            └──Type expr: Variable: 15004
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: segment
                               └──Type expr: Variable: 15003
                               └──Type expr: Variable: 15004
                            └──Desc: Variable: seg
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: segment
                                     └──Type expr: Variable: 15003
                                     └──Type expr: Variable: 15004
                                  └──Desc: Variable
                                     └──Variable: seg
                               └──Type expr: Constructor: segment
                                  └──Type expr: Variable: 15003
                                  └──Type expr: Variable: 15004
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: segment
                                           └──Type expr: Variable: 15003
                                           └──Type expr: Variable: 15004
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Seg_nil
                                              └──Constructor type:
                                                 └──Type expr: Constructor: segment
                                                    └──Type expr: Variable: 15003
                                                    └──Type expr: Variable: 15004
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 0
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: segment
                                           └──Type expr: Variable: 15003
                                           └──Type expr: Variable: 15004
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Seg_cons
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: segment
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 15003
                                                       └──Type expr: Variable: 15003
                                                    └──Type expr: Variable: 15004
                                              └──Constructor type:
                                                 └──Type expr: Constructor: segment
                                                    └──Type expr: Variable: 15003
                                                    └──Type expr: Variable: 15004
                                           └──Pattern:
                                              └──Type expr: Constructor: segment
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 15003
                                                    └──Type expr: Variable: 15003
                                                 └──Type expr: Variable: 15004
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Seg_nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: segment
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 15003
                                                             └──Type expr: Variable: 15003
                                                          └──Type expr: Variable: 15004
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 0
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: segment
                                           └──Type expr: Variable: 15003
                                           └──Type expr: Variable: 15004
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Seg_cons
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: segment
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 15003
                                                       └──Type expr: Variable: 15003
                                                    └──Type expr: Variable: 15004
                                              └──Constructor type:
                                                 └──Type expr: Constructor: segment
                                                    └──Type expr: Variable: 15003
                                                    └──Type expr: Variable: 15004
                                           └──Pattern:
                                              └──Type expr: Constructor: segment
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 15003
                                                    └──Type expr: Variable: 15003
                                                 └──Type expr: Variable: 15004
                                              └──Desc: Any
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 0 |}]

let%expect_test "" = 
  let str = 
    {|
      type ('a, 'b) segment = 
        | Seg_nil constraint 'a = 'b
        | Seg_cons of ('a * 'a, 'b) segment 
      ;;


      let color = 
        fun seg ->
          match seg with
          ( Seg_nil -> 0
          | Seg_cons Seg_nil -> 0
          | Seg_cons _ -> 0
          )
      ;;
    |}
  in
  print_infer_result str;
  [%expect {| "Non rigid equations" |}]