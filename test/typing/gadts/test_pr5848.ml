open! Import
open Util

let%expect_test "" = 
  let str = 
    {|
      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;

      external magic : 'a 'b. 'a -> 'b = "%magic";;

      let (type 'a 'b) f = 
        fun (t1 : 'a) (t2 : 'b) ->
          (magic Refl : ('a, 'b) eq)
      ;;

      let (type 'a) of_type = 
        fun (x : 'a) ->
          (match f x 4 with ( Refl -> 5 ) : 'a)
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: eq
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Refl
                   └──Constructor alphas: 16823 16824
                   └──Constructor type:
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: 16823
                         └──Type expr: Variable: 16824
                   └──Constraint:
                      └──Type expr: Variable: 16823
                      └──Type expr: Variable: 16824
       └──Structure item: Primitive
          └──Value description:
             └──Name: magic
             └──Scheme:
                └──Variables: 16827,16826
                └──Type expr: Arrow
                   └──Type expr: Variable: 16826
                   └──Type expr: Variable: 16827
             └──Primitive name: %magic
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 16835
                      └──Type expr: Arrow
                         └──Type expr: Variable: 16841
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: 16835
                            └──Type expr: Variable: 16841
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: 16835,16841
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 16835
                         └──Type expr: Arrow
                            └──Type expr: Variable: 16841
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: 16835
                               └──Type expr: Variable: 16841
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 16835
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: 16841
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: 16835
                                  └──Type expr: Variable: 16841
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: 16841
                                  └──Desc: Variable: t2
                               └──Expression:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: 16835
                                     └──Type expr: Variable: 16841
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: 16857
                                              └──Type expr: Variable: 16857
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: 16835
                                              └──Type expr: Variable: 16841
                                        └──Desc: Variable
                                           └──Variable: magic
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: 16835
                                              └──Type expr: Variable: 16841
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: 16857
                                              └──Type expr: Variable: 16857
                                     └──Expression:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: 16857
                                           └──Type expr: Variable: 16857
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Refl
                                              └──Constructor type:
                                                 └──Type expr: Constructor: eq
                                                    └──Type expr: Variable: 16857
                                                    └──Type expr: Variable: 16857
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 16868
                      └──Type expr: Variable: 16868
                   └──Desc: Variable: of_type
                └──Abstraction:
                   └──Variables: 16868
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 16868
                         └──Type expr: Variable: 16868
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 16868
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: 16868
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: 16868
                                     └──Type expr: Constructor: int
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: int
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: 16868
                                              └──Type expr: Constructor: int
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: 16868
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: 16868
                                                       └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: f
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Variable: 16868
                                           └──Expression:
                                              └──Type expr: Variable: 16868
                                              └──Desc: Variable
                                                 └──Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 4
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: 16868
                                  └──Type expr: Constructor: int
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: 16868
                                           └──Type expr: Constructor: int
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Refl
                                              └──Constructor type:
                                                 └──Type expr: Constructor: eq
                                                    └──Type expr: Variable: 16868
                                                    └──Type expr: Constructor: int
                                     └──Expression:
                                        └──Type expr: Variable: 16868
                                        └──Desc: Constant: 5 |}]