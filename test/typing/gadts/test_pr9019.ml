open! Import
open Util

let%expect_test "" = 
  let str = 
    {|
      type ab = A | B;;

      type mab = ab;;
      type 'a t = 
        | Ab constraint 'a = ab
        | Mab constraint 'a = mab
      ;;

      let ab = Ab;;

      let (type 't) f =
        fun (t1 : 't t) (t2 : 't t) (x : 't) ->
          match (t1, t2) with
          ( (Ab, Ab) -> match x with ( A -> 1 )
          | (Mab, _) -> match x with ( A -> 2 )
          | (_, Ab) -> match x with ( B -> 3 )
          | (_, Mab) -> match x with ( B -> 4 )
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
             └──Type name: ab
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: A
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: ab
                └──Constructor declaration:
                   └──Constructor name: B
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: ab
       └──Structure item: Type
          └──Type declaration:
             └──Type name: mab
             └──Type declaration kind: Alias
                └──Alias
                   └──Alias name: mab
                   └──Alias alphas:
                   └──Type expr: Constructor: ab
       └──Structure item: Type
          └──Type declaration:
             └──Type name: t
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Ab
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: ab
                └──Constructor declaration:
                   └──Constructor name: Mab
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: mab
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: t
                      └──Type expr: Constructor: ab
                   └──Desc: Variable: ab
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: t
                         └──Type expr: Constructor: ab
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: Ab
                            └──Constructor type:
                               └──Type expr: Constructor: t
                                  └──Type expr: Constructor: ab
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a5150
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: a5150
                         └──Type expr: Arrow
                            └──Type expr: Variable: a5150
                            └──Type expr: Constructor: int
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: a5150
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: a5150
                         └──Type expr: Arrow
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: a5150
                            └──Type expr: Arrow
                               └──Type expr: Variable: a5150
                               └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: a5150
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: a5150
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a5150
                                  └──Type expr: Constructor: int
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: a5150
                                  └──Desc: Variable: t2
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a5150
                                     └──Type expr: Constructor: int
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: a5150
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: a5150
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: a5150
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Constructor: t
                                                       └──Type expr: Variable: a5150
                                                    └──Desc: Variable
                                                       └──Variable: t1
                                                 └──Expression:
                                                    └──Type expr: Constructor: t
                                                       └──Type expr: Variable: a5150
                                                    └──Desc: Variable
                                                       └──Variable: t2
                                           └──Type expr: Tuple
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Variable: a5150
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Variable: a5150
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: a5150
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: a5150
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: t
                                                             └──Type expr: Variable: a5150
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Ab
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: t
                                                                      └──Type expr: Variable: a5150
                                                       └──Pattern:
                                                          └──Type expr: Constructor: t
                                                             └──Type expr: Variable: a5150
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Ab
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: t
                                                                      └──Type expr: Variable: a5150
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Match
                                                       └──Expression:
                                                          └──Type expr: Variable: a5150
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                       └──Type expr: Variable: a5150
                                                       └──Cases:
                                                          └──Case:
                                                             └──Pattern:
                                                                └──Type expr: Variable: a5150
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: A
                                                                      └──Constructor type:
                                                                         └──Type expr: Variable: a5150
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Constant: 1
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: a5150
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: a5150
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: t
                                                             └──Type expr: Variable: a5150
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Mab
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: t
                                                                      └──Type expr: Variable: a5150
                                                       └──Pattern:
                                                          └──Type expr: Constructor: t
                                                             └──Type expr: Variable: a5150
                                                          └──Desc: Any
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Match
                                                       └──Expression:
                                                          └──Type expr: Variable: a5150
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                       └──Type expr: Variable: a5150
                                                       └──Cases:
                                                          └──Case:
                                                             └──Pattern:
                                                                └──Type expr: Variable: a5150
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: A
                                                                      └──Constructor type:
                                                                         └──Type expr: Variable: a5150
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Constant: 2
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: a5150
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: a5150
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: t
                                                             └──Type expr: Variable: a5150
                                                          └──Desc: Any
                                                       └──Pattern:
                                                          └──Type expr: Constructor: t
                                                             └──Type expr: Variable: a5150
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Ab
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: t
                                                                      └──Type expr: Variable: a5150
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Match
                                                       └──Expression:
                                                          └──Type expr: Variable: a5150
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                       └──Type expr: Variable: a5150
                                                       └──Cases:
                                                          └──Case:
                                                             └──Pattern:
                                                                └──Type expr: Variable: a5150
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: B
                                                                      └──Constructor type:
                                                                         └──Type expr: Variable: a5150
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Constant: 3
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: a5150
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: a5150
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: t
                                                             └──Type expr: Variable: a5150
                                                          └──Desc: Any
                                                       └──Pattern:
                                                          └──Type expr: Constructor: t
                                                             └──Type expr: Variable: a5150
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Mab
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: t
                                                                      └──Type expr: Variable: a5150
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Match
                                                       └──Expression:
                                                          └──Type expr: Variable: a5150
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                       └──Type expr: Variable: a5150
                                                       └──Cases:
                                                          └──Case:
                                                             └──Pattern:
                                                                └──Type expr: Variable: a5150
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: B
                                                                      └──Constructor type:
                                                                         └──Type expr: Variable: a5150
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Constant: 4 |}]

let%expect_test "" = 
  let str = 
    {|
      type 'a ab = A | B;;

      type 'a mab = 'a ab;;  
      type 'a t = 
        | Ab constraint 'a = unit ab
        | Mab constraint 'a = unit mab
      ;;   

      let ab = Ab;;
      let a = A;;
      let b = B;;

      let (type 'a) f = 
        fun (t1 : 'a t) (t2 : 'a t) (x : 'a) ->
          match (t1, t2) with
          ( (Ab, Ab) -> match x with ( A -> 1 )
          | (_, Ab) -> match x with ( A -> 2 )
          | (_, Ab) -> match x with ( B -> 3 )
          | (_, Mab) -> 4
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
             └──Type name: ab
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: A
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: ab
                         └──Type expr: Variable: a
                └──Constructor declaration:
                   └──Constructor name: B
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: ab
                         └──Type expr: Variable: a
       └──Structure item: Type
          └──Type declaration:
             └──Type name: mab
             └──Type declaration kind: Alias
                └──Alias
                   └──Alias name: mab
                   └──Alias alphas: a
                   └──Type expr: Constructor: ab
                      └──Type expr: Variable: a
       └──Structure item: Type
          └──Type declaration:
             └──Type name: t
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Ab
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: ab
                         └──Type expr: Constructor: unit
                └──Constructor declaration:
                   └──Constructor name: Mab
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: mab
                         └──Type expr: Constructor: unit
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: t
                      └──Type expr: Constructor: ab
                         └──Type expr: Constructor: unit
                   └──Desc: Variable: ab
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: t
                         └──Type expr: Constructor: ab
                            └──Type expr: Constructor: unit
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: Ab
                            └──Constructor type:
                               └──Type expr: Constructor: t
                                  └──Type expr: Constructor: ab
                                     └──Type expr: Constructor: unit
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: ab
                      └──Type expr: Variable: a5254
                   └──Desc: Variable: a
                └──Abstraction:
                   └──Variables: a5254
                   └──Expression:
                      └──Type expr: Constructor: ab
                         └──Type expr: Variable: a5254
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: A
                            └──Constructor type:
                               └──Type expr: Constructor: ab
                                  └──Type expr: Variable: a5254
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: ab
                      └──Type expr: Variable: a5258
                   └──Desc: Variable: b
                └──Abstraction:
                   └──Variables: a5258
                   └──Expression:
                      └──Type expr: Constructor: ab
                         └──Type expr: Variable: a5258
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: B
                            └──Constructor type:
                               └──Type expr: Constructor: ab
                                  └──Type expr: Variable: a5258
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a5270
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: a5270
                         └──Type expr: Arrow
                            └──Type expr: Variable: a5270
                            └──Type expr: Constructor: int
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: a5270
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: a5270
                         └──Type expr: Arrow
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: a5270
                            └──Type expr: Arrow
                               └──Type expr: Variable: a5270
                               └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: a5270
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: a5270
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a5270
                                  └──Type expr: Constructor: int
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: a5270
                                  └──Desc: Variable: t2
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a5270
                                     └──Type expr: Constructor: int
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: a5270
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: a5270
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: a5270
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Constructor: t
                                                       └──Type expr: Variable: a5270
                                                    └──Desc: Variable
                                                       └──Variable: t1
                                                 └──Expression:
                                                    └──Type expr: Constructor: t
                                                       └──Type expr: Variable: a5270
                                                    └──Desc: Variable
                                                       └──Variable: t2
                                           └──Type expr: Tuple
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Variable: a5270
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Variable: a5270
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: a5270
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: a5270
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: t
                                                             └──Type expr: Variable: a5270
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Ab
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: t
                                                                      └──Type expr: Variable: a5270
                                                       └──Pattern:
                                                          └──Type expr: Constructor: t
                                                             └──Type expr: Variable: a5270
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Ab
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: t
                                                                      └──Type expr: Variable: a5270
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Match
                                                       └──Expression:
                                                          └──Type expr: Variable: a5270
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                       └──Type expr: Variable: a5270
                                                       └──Cases:
                                                          └──Case:
                                                             └──Pattern:
                                                                └──Type expr: Variable: a5270
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: A
                                                                      └──Constructor type:
                                                                         └──Type expr: Variable: a5270
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Constant: 1
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: a5270
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: a5270
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: t
                                                             └──Type expr: Variable: a5270
                                                          └──Desc: Any
                                                       └──Pattern:
                                                          └──Type expr: Constructor: t
                                                             └──Type expr: Variable: a5270
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Ab
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: t
                                                                      └──Type expr: Variable: a5270
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Match
                                                       └──Expression:
                                                          └──Type expr: Variable: a5270
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                       └──Type expr: Variable: a5270
                                                       └──Cases:
                                                          └──Case:
                                                             └──Pattern:
                                                                └──Type expr: Variable: a5270
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: A
                                                                      └──Constructor type:
                                                                         └──Type expr: Variable: a5270
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Constant: 2
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: a5270
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: a5270
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: t
                                                             └──Type expr: Variable: a5270
                                                          └──Desc: Any
                                                       └──Pattern:
                                                          └──Type expr: Constructor: t
                                                             └──Type expr: Variable: a5270
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Ab
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: t
                                                                      └──Type expr: Variable: a5270
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Match
                                                       └──Expression:
                                                          └──Type expr: Variable: a5270
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                       └──Type expr: Variable: a5270
                                                       └──Cases:
                                                          └──Case:
                                                             └──Pattern:
                                                                └──Type expr: Variable: a5270
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: B
                                                                      └──Constructor type:
                                                                         └──Type expr: Variable: a5270
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Constant: 3
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: a5270
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: a5270
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: t
                                                             └──Type expr: Variable: a5270
                                                          └──Desc: Any
                                                       └──Pattern:
                                                          └──Type expr: Constructor: t
                                                             └──Type expr: Variable: a5270
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Mab
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: t
                                                                      └──Type expr: Variable: a5270
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Constant: 4 |}]