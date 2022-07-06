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
                   └──Constructor alphas: 39 40
                   └──Constructor type:
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: 39
                         └──Type expr: Variable: 40
                   └──Constraint:
                      └──Type expr: Variable: 39
                      └──Type expr: Variable: 40
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
                └──Variables: 0
                └──Type expr: Variable: 0
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
                      └──Type expr: Variable: 3
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: 3,3
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Foo
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: empty
                               └──Type expr: Row uniform
                                  └──Type expr: Constructor: absent
                         └──Type expr: Variable: 3
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
                            └──Type expr: Variable: 3
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
                                        └──Type expr: Variable: 3
                                        └──Desc: Variable
                                           └──Variable: hole
                                           └──Type expr: Variable: 3 |}]