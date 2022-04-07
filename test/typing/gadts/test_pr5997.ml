open! Import
open Util

let%expect_test "" = 
  let str = 
    {|
      type ('a, 'b) cmp = 
        | Eq constraint 'a = 'b
        | Diff
      ;;

      type u_t = T;;
      type m_t = u_t;;
      let comp1 = (Eq : (u_t, m_t) cmp);;

      let _ = 
        match comp1 with
        ( Eq -> true 
        | Diff -> false
        )
      ;;

      type a_t = { x : int };;
      type b_t = a_t;;
      let comp2 = (Eq : (a_t, b_t) cmp);;

      let _ = 
        match comp2 with
        ( Eq -> true 
        | Diff -> false
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
             └──Type name: cmp
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Eq
                   └──Constructor alphas: a b
                   └──Constructor type:
                      └──Type expr: Constructor: cmp
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Variable: b
                └──Constructor declaration:
                   └──Constructor name: Diff
                   └──Constructor alphas: a b
                   └──Constructor type:
                      └──Type expr: Constructor: cmp
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
       └──Structure item: Type
          └──Type declaration:
             └──Type name: u_t
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: T
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: u_t
       └──Structure item: Type
          └──Type declaration:
             └──Type name: m_t
             └──Type declaration kind: Alias
                └──Alias
                   └──Alias name: m_t
                   └──Alias alphas:
                   └──Type expr: Constructor: u_t
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: cmp
                      └──Type expr: Constructor: u_t
                      └──Type expr: Constructor: m_t
                   └──Desc: Variable: comp1
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: cmp
                         └──Type expr: Constructor: u_t
                         └──Type expr: Constructor: m_t
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: Eq
                            └──Constructor type:
                               └──Type expr: Constructor: cmp
                                  └──Type expr: Constructor: u_t
                                  └──Type expr: Constructor: u_t
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: bool
                   └──Desc: Any
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: bool
                      └──Desc: Match
                         └──Expression:
                            └──Type expr: Constructor: cmp
                               └──Type expr: Constructor: u_t
                               └──Type expr: Constructor: m_t
                            └──Desc: Variable
                               └──Variable: comp1
                         └──Type expr: Constructor: cmp
                            └──Type expr: Constructor: u_t
                            └──Type expr: Constructor: m_t
                         └──Cases:
                            └──Case:
                               └──Pattern:
                                  └──Type expr: Constructor: cmp
                                     └──Type expr: Constructor: u_t
                                     └──Type expr: Constructor: m_t
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Eq
                                        └──Constructor type:
                                           └──Type expr: Constructor: cmp
                                              └──Type expr: Constructor: u_t
                                              └──Type expr: Constructor: m_t
                               └──Expression:
                                  └──Type expr: Constructor: bool
                                  └──Desc: Constant: true
                            └──Case:
                               └──Pattern:
                                  └──Type expr: Constructor: cmp
                                     └──Type expr: Constructor: u_t
                                     └──Type expr: Constructor: m_t
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Diff
                                        └──Constructor type:
                                           └──Type expr: Constructor: cmp
                                              └──Type expr: Constructor: u_t
                                              └──Type expr: Constructor: m_t
                               └──Expression:
                                  └──Type expr: Constructor: bool
                                  └──Desc: Constant: false
       └──Structure item: Type
          └──Type declaration:
             └──Type name: a_t
             └──Type declaration kind: Record
                └──Label declaration:
                   └──Label name: x
                   └──Label alphas:
                   └──Label betas:
                   └──Type expr: Constructor: int
                   └──Type expr: Constructor: a_t
       └──Structure item: Type
          └──Type declaration:
             └──Type name: b_t
             └──Type declaration kind: Alias
                └──Alias
                   └──Alias name: b_t
                   └──Alias alphas:
                   └──Type expr: Constructor: a_t
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: cmp
                      └──Type expr: Constructor: a_t
                      └──Type expr: Constructor: b_t
                   └──Desc: Variable: comp2
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: cmp
                         └──Type expr: Constructor: a_t
                         └──Type expr: Constructor: b_t
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: Eq
                            └──Constructor type:
                               └──Type expr: Constructor: cmp
                                  └──Type expr: Constructor: a_t
                                  └──Type expr: Constructor: a_t
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: bool
                   └──Desc: Any
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: bool
                      └──Desc: Match
                         └──Expression:
                            └──Type expr: Constructor: cmp
                               └──Type expr: Constructor: a_t
                               └──Type expr: Constructor: b_t
                            └──Desc: Variable
                               └──Variable: comp2
                         └──Type expr: Constructor: cmp
                            └──Type expr: Constructor: a_t
                            └──Type expr: Constructor: b_t
                         └──Cases:
                            └──Case:
                               └──Pattern:
                                  └──Type expr: Constructor: cmp
                                     └──Type expr: Constructor: a_t
                                     └──Type expr: Constructor: b_t
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Eq
                                        └──Constructor type:
                                           └──Type expr: Constructor: cmp
                                              └──Type expr: Constructor: a_t
                                              └──Type expr: Constructor: b_t
                               └──Expression:
                                  └──Type expr: Constructor: bool
                                  └──Desc: Constant: true
                            └──Case:
                               └──Pattern:
                                  └──Type expr: Constructor: cmp
                                     └──Type expr: Constructor: a_t
                                     └──Type expr: Constructor: b_t
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Diff
                                        └──Constructor type:
                                           └──Type expr: Constructor: cmp
                                              └──Type expr: Constructor: a_t
                                              └──Type expr: Constructor: b_t
                               └──Expression:
                                  └──Type expr: Constructor: bool
                                  └──Desc: Constant: false |}]