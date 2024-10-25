open! Import
open Util

let%expect_test "" =
  let str =
    {|
      type 'a general = 
        { indir : 'a desc; unit_ : unit }
      and 'a desc = 
        | C of unit general constraint 'a = unit
      ;;

      let rec (type 'k) foo = 
        fun (g : 'k general) ->
          (match g.indir with
           ( C g' -> 
              let new_g' = foo g' in
              if true then
                { indir = C new_g'; unit_ = g.unit_ }
              else 
                new_g'  
           | indir' ->
              { indir = indir'; unit_ = g.unit_ } 
           )
          : 'k general)
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: general
             └──Type declaration kind: Record
                └──Label declaration:
                   └──Label name: indir
                   └──Label alphas: 0
                   └──Label betas:
                   └──Type expr: Constructor: desc
                      └──Type expr: Variable: 0
                   └──Type expr: Constructor: general
                      └──Type expr: Variable: 0
                └──Label declaration:
                   └──Label name: unit_
                   └──Label alphas: 0
                   └──Label betas:
                   └──Type expr: Constructor: unit
                   └──Type expr: Constructor: general
                      └──Type expr: Variable: 0
          └──Type declaration:
             └──Type name: desc
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: C
                   └──Constructor alphas: 5
                   └──Constructor type:
                      └──Type expr: Constructor: desc
                         └──Type expr: Variable: 5
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: general
                         └──Type expr: Constructor: unit
                   └──Constraint:
                      └──Type expr: Variable: 5
                      └──Type expr: Constructor: unit
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: foo
                └──Abstraction:
                   └──Variables: 6
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: general
                            └──Type expr: Variable: 25
                         └──Type expr: Constructor: general
                            └──Type expr: Variable: 25
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: general
                               └──Type expr: Variable: 25
                            └──Desc: Variable: g
                         └──Expression:
                            └──Type expr: Constructor: general
                               └──Type expr: Variable: 25
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: desc
                                     └──Type expr: Variable: 25
                                  └──Desc: Field
                                     └──Expression:
                                        └──Type expr: Constructor: general
                                           └──Type expr: Variable: 25
                                        └──Desc: Variable
                                           └──Variable: g
                                     └──Label description:
                                        └──Label: indir
                                        └──Label argument type:
                                           └──Type expr: Constructor: desc
                                              └──Type expr: Variable: 25
                                        └──Label type:
                                           └──Type expr: Constructor: general
                                              └──Type expr: Variable: 25
                               └──Type expr: Constructor: desc
                                  └──Type expr: Variable: 25
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: desc
                                           └──Type expr: Variable: 25
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: C
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: general
                                                    └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: desc
                                                    └──Type expr: Variable: 25
                                           └──Pattern:
                                              └──Type expr: Constructor: general
                                                 └──Type expr: Constructor: unit
                                              └──Desc: Variable: g'
                                     └──Expression:
                                        └──Type expr: Constructor: general
                                           └──Type expr: Variable: 25
                                        └──Desc: Let
                                           └──Value bindings:
                                              └──Value binding:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: general
                                                       └──Type expr: Variable: 25
                                                    └──Desc: Variable: new_g'
                                                 └──Abstraction:
                                                    └──Variables:
                                                    └──Expression:
                                                       └──Type expr: Constructor: general
                                                          └──Type expr: Variable: 25
                                                       └──Desc: Application
                                                          └──Expression:
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: general
                                                                   └──Type expr: Variable: 25
                                                                └──Type expr: Constructor: general
                                                                   └──Type expr: Variable: 25
                                                             └──Desc: Variable
                                                                └──Variable: foo
                                                                └──Type expr: Variable: 25
                                                          └──Expression:
                                                             └──Type expr: Constructor: general
                                                                └──Type expr: Variable: 25
                                                             └──Desc: Variable
                                                                └──Variable: g'
                                           └──Expression:
                                              └──Type expr: Constructor: general
                                                 └──Type expr: Variable: 25
                                              └──Desc: If
                                                 └──Expression:
                                                    └──Type expr: Constructor: bool
                                                    └──Desc: Constant: true
                                                 └──Expression:
                                                    └──Type expr: Constructor: general
                                                       └──Type expr: Variable: 25
                                                    └──Desc: Record
                                                       └──Label description:
                                                          └──Label: indir
                                                          └──Label argument type:
                                                             └──Type expr: Constructor: desc
                                                                └──Type expr: Variable: 25
                                                          └──Label type:
                                                             └──Type expr: Constructor: general
                                                                └──Type expr: Variable: 25
                                                       └──Expression:
                                                          └──Type expr: Constructor: desc
                                                             └──Type expr: Variable: 25
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: C
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: general
                                                                      └──Type expr: Variable: 25
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: desc
                                                                      └──Type expr: Variable: 25
                                                             └──Expression:
                                                                └──Type expr: Constructor: general
                                                                   └──Type expr: Variable: 25
                                                                └──Desc: Variable
                                                                   └──Variable: new_g'
                                                       └──Label description:
                                                          └──Label: unit_
                                                          └──Label argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Label type:
                                                             └──Type expr: Constructor: general
                                                                └──Type expr: Variable: 25
                                                       └──Expression:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Field
                                                             └──Expression:
                                                                └──Type expr: Constructor: general
                                                                   └──Type expr: Variable: 25
                                                                └──Desc: Variable
                                                                   └──Variable: g
                                                             └──Label description:
                                                                └──Label: unit_
                                                                └──Label argument type:
                                                                   └──Type expr: Constructor: unit
                                                                └──Label type:
                                                                   └──Type expr: Constructor: general
                                                                      └──Type expr: Variable: 25
                                                 └──Expression:
                                                    └──Type expr: Constructor: general
                                                       └──Type expr: Variable: 25
                                                    └──Desc: Variable
                                                       └──Variable: new_g'
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: desc
                                           └──Type expr: Variable: 25
                                        └──Desc: Variable: indir'
                                     └──Expression:
                                        └──Type expr: Constructor: general
                                           └──Type expr: Variable: 25
                                        └──Desc: Record
                                           └──Label description:
                                              └──Label: indir
                                              └──Label argument type:
                                                 └──Type expr: Constructor: desc
                                                    └──Type expr: Variable: 25
                                              └──Label type:
                                                 └──Type expr: Constructor: general
                                                    └──Type expr: Variable: 25
                                           └──Expression:
                                              └──Type expr: Constructor: desc
                                                 └──Type expr: Variable: 25
                                              └──Desc: Variable
                                                 └──Variable: indir'
                                           └──Label description:
                                              └──Label: unit_
                                              └──Label argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Label type:
                                                 └──Type expr: Constructor: general
                                                    └──Type expr: Variable: 25
                                           └──Expression:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Field
                                                 └──Expression:
                                                    └──Type expr: Constructor: general
                                                       └──Type expr: Variable: 25
                                                    └──Desc: Variable
                                                       └──Variable: g
                                                 └──Label description:
                                                    └──Label: unit_
                                                    └──Label argument type:
                                                       └──Type expr: Constructor: unit
                                                    └──Label type:
                                                       └──Type expr: Constructor: general
                                                          └──Type expr: Variable: 25 |}]
