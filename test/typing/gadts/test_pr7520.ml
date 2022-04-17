open! Import
open Util

let%expect_test "" = 
  let str = 
    {|
      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;
      type empty = (int, string) eq;;

      external hole : 'a. 'a = "%hole";;

      let f = 
        fun t ->
          match t with (`Foo (_ : empty) -> hole)
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
                   └──Constructor alphas: 15299 15300
                   └──Constructor type:
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: 15299
                         └──Type expr: Variable: 15300
                   └──Constraint:
                      └──Type expr: Variable: 15299
                      └──Type expr: Variable: 15300
       └──Structure item: Type
          └──Type declaration:
             └──Type name: empty
             └──Type declaration kind: Alias
                └──Alias
                   └──Alias name: empty
                   └──Alias alphas:
                   └──Type expr: Constructor: eq
                      └──Type expr: Constructor: int
                      └──Type expr: Constructor: string
       └──Structure item: Primitive
          └──Value description:
             └──Name: hole
             └──Scheme:
                └──Variables: 15305
                └──Type expr: Variable: 15305
             └──Primitive name: %hole
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Foo
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: empty
                            └──Type expr: Row uniform
                               └──Type expr: Constructor: absent
                      └──Type expr: Variable: 15308
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: 15308,15308
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Foo
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: empty
                               └──Type expr: Row uniform
                                  └──Type expr: Constructor: absent
                         └──Type expr: Variable: 15308
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Foo
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: empty
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Variable: 15308
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Foo
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: empty
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Foo
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: empty
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Foo
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: empty
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Foo
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: Foo
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: empty
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                           └──Pattern:
                                              └──Type expr: Constructor: empty
                                              └──Desc: Any
                                     └──Expression:
                                        └──Type expr: Variable: 15308
                                        └──Desc: Variable
                                           └──Variable: hole
                                           └──Type expr: Variable: 15308 |}]