open! Import
open Util

let%expect_test "poly-1" =
  let str = 
    {|
      type 'a t = { t : 'a };;
      type 'a fold = { fold : 'b. ('b -> 'a -> 'b) -> 'b -> 'b };;

      type 'a list = 
        | Nil
        | Cons of 'a * 'a list
      ;;
      external fold_left : 'a 'b. 'a list -> ('b -> 'a -> 'b) -> 'b -> 'b = "%fold_left";;

      let f = fun xs -> { fold = fold_left xs };;
      let _ = 
        let xs = Cons (1, Cons (2, Cons (3, Nil))) in
        (f xs).fold (fun x y -> x + y) 0
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
             └──Type declaration kind: Record
                └──Label declaration:
                   └──Label name: t
                   └──Label alphas: 27696
                   └──Label betas:
                   └──Type expr: Variable: 27696
                   └──Type expr: Constructor: t
                      └──Type expr: Variable: 27696
       └──Structure item: Type
          └──Type declaration:
             └──Type name: fold
             └──Type declaration kind: Record
                └──Label declaration:
                   └──Label name: fold
                   └──Label alphas: 27698
                   └──Label betas: 27699
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: 27699
                         └──Type expr: Arrow
                            └──Type expr: Variable: 27698
                            └──Type expr: Variable: 27699
                      └──Type expr: Arrow
                         └──Type expr: Variable: 27699
                         └──Type expr: Variable: 27699
                   └──Type expr: Constructor: fold
                      └──Type expr: Variable: 27698
       └──Structure item: Type
          └──Type declaration:
             └──Type name: list
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: 27705
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 27705
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 27705
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 27705
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: 27705
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 27705
       └──Structure item: Primitive
          └──Value description:
             └──Name: fold_left
             └──Scheme:
                └──Variables: 27711,27710
                └──Type expr: Arrow
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: 27710
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: 27711
                         └──Type expr: Arrow
                            └──Type expr: Variable: 27710
                            └──Type expr: Variable: 27711
                      └──Type expr: Arrow
                         └──Type expr: Variable: 27711
                         └──Type expr: Variable: 27711
             └──Primitive name: %fold_left
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 27729
                      └──Type expr: Constructor: fold
                         └──Type expr: Variable: 27729
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 27729
                         └──Type expr: Constructor: fold
                            └──Type expr: Variable: 27729
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: 27729
                            └──Desc: Variable: xs
                         └──Expression:
                            └──Type expr: Constructor: fold
                               └──Type expr: Variable: 27729
                            └──Desc: Record
                               └──Label description:
                                  └──Label: fold
                                  └──Label argument type:
                                     └──Type expr: Arrow
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: 27737
                                           └──Type expr: Arrow
                                              └──Type expr: Variable: 27729
                                              └──Type expr: Variable: 27737
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: 27737
                                           └──Type expr: Variable: 27737
                                  └──Label type:
                                     └──Type expr: Constructor: fold
                                        └──Type expr: Variable: 27729
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: 27737
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: 27729
                                           └──Type expr: Variable: 27737
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: 27737
                                        └──Type expr: Variable: 27737
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: 27729
                                           └──Type expr: Arrow
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: 27737
                                                 └──Type expr: Arrow
                                                    └──Type expr: Variable: 27729
                                                    └──Type expr: Variable: 27737
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: 27737
                                                 └──Type expr: Variable: 27737
                                        └──Desc: Variable
                                           └──Variable: fold_left
                                           └──Type expr: Variable: 27737
                                           └──Type expr: Variable: 27729
                                     └──Expression:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Variable: 27729
                                        └──Desc: Variable
                                           └──Variable: xs
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: int
                   └──Desc: Any
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: int
                      └──Desc: Let
                         └──Value bindings:
                            └──Value binding:
                               └──Pattern:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Constructor: int
                                  └──Desc: Variable: xs
                               └──Abstraction:
                                  └──Variables:
                                  └──Expression:
                                     └──Type expr: Constructor: list
                                        └──Type expr: Constructor: int
                                     └──Desc: Construct
                                        └──Constructor description:
                                           └──Name: Cons
                                           └──Constructor argument type:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: int
                                           └──Constructor type:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Constructor: int
                                        └──Expression:
                                           └──Type expr: Tuple
                                              └──Type expr: Constructor: int
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Constructor: int
                                           └──Desc: Tuple
                                              └──Expression:
                                                 └──Type expr: Constructor: int
                                                 └──Desc: Constant: 1
                                              └──Expression:
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: int
                                                 └──Desc: Construct
                                                    └──Constructor description:
                                                       └──Name: Cons
                                                       └──Constructor argument type:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                       └──Constructor type:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: int
                                                    └──Expression:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: int
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: int
                                                       └──Desc: Tuple
                                                          └──Expression:
                                                             └──Type expr: Constructor: int
                                                             └──Desc: Constant: 2
                                                          └──Expression:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                             └──Desc: Construct
                                                                └──Constructor description:
                                                                   └──Name: Cons
                                                                   └──Constructor argument type:
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Constructor: int
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Constructor: int
                                                                   └──Constructor type:
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: int
                                                                └──Expression:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: int
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: int
                                                                   └──Desc: Tuple
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: int
                                                                         └──Desc: Constant: 3
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Constructor: int
                                                                         └──Desc: Construct
                                                                            └──Constructor description:
                                                                               └──Name: Nil
                                                                               └──Constructor type:
                                                                                  └──Type expr: Constructor: list
                                                                                     └──Type expr: Constructor: int
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: int
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: int
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: int
                                              └──Type expr: Constructor: int
                                        └──Desc: Field
                                           └──Expression:
                                              └──Type expr: Constructor: fold
                                                 └──Type expr: Constructor: int
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Constructor: int
                                                       └──Type expr: Constructor: fold
                                                          └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: f
                                                       └──Type expr: Constructor: int
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: xs
                                           └──Label description:
                                              └──Label: fold
                                              └──Label argument type:
                                                 └──Type expr: Arrow
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: int
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: int
                                                          └──Type expr: Constructor: int
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: int
                                                       └──Type expr: Constructor: int
                                              └──Label type:
                                                 └──Type expr: Constructor: fold
                                                    └──Type expr: Constructor: int
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: int
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: int
                                              └──Type expr: Constructor: int
                                        └──Desc: Function
                                           └──Pattern:
                                              └──Type expr: Constructor: int
                                              └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                              └──Desc: Function
                                                 └──Pattern:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable: y
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: int
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: int
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: int
                                                                      └──Type expr: Constructor: int
                                                                └──Desc: Primitive: (+)
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: y
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Constant: 0 |}]

let%expect_test "poly-2" =
  let str = 
    {|
      type id = { id : 'a. 'a -> 'a };;

      let id = fun x -> x;;
      let id = 
        let boxed_id = id { id = id } in boxed_id.id
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: id
             └──Type declaration kind: Record
                └──Label declaration:
                   └──Label name: id
                   └──Label alphas:
                   └──Label betas: 27854
                   └──Type expr: Arrow
                      └──Type expr: Variable: 27854
                      └──Type expr: Variable: 27854
                   └──Type expr: Constructor: id
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 27859
                      └──Type expr: Variable: 27859
                   └──Desc: Variable: id
                └──Abstraction:
                   └──Variables: 27859,27859
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 27859
                         └──Type expr: Variable: 27859
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 27859
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: 27859
                            └──Desc: Variable
                               └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 27879
                      └──Type expr: Variable: 27879
                   └──Desc: Variable: id
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 27879
                         └──Type expr: Variable: 27879
                      └──Desc: Let
                         └──Value bindings:
                            └──Value binding:
                               └──Pattern:
                                  └──Type expr: Constructor: id
                                  └──Desc: Variable: boxed_id
                               └──Abstraction:
                                  └──Variables:
                                  └──Expression:
                                     └──Type expr: Constructor: id
                                     └──Desc: Application
                                        └──Expression:
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: id
                                              └──Type expr: Constructor: id
                                           └──Desc: Variable
                                              └──Variable: id
                                              └──Type expr: Constructor: id
                                        └──Expression:
                                           └──Type expr: Constructor: id
                                           └──Desc: Record
                                              └──Label description:
                                                 └──Label: id
                                                 └──Label argument type:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: 27872
                                                       └──Type expr: Variable: 27872
                                                 └──Label type:
                                                    └──Type expr: Constructor: id
                                              └──Expression:
                                                 └──Type expr: Arrow
                                                    └──Type expr: Variable: 27872
                                                    └──Type expr: Variable: 27872
                                                 └──Desc: Variable
                                                    └──Variable: id
                                                    └──Type expr: Variable: 27872
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: 27879
                               └──Type expr: Variable: 27879
                            └──Desc: Field
                               └──Expression:
                                  └──Type expr: Constructor: id
                                  └──Desc: Variable
                                     └──Variable: boxed_id
                               └──Label description:
                                  └──Label: id
                                  └──Label argument type:
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: 27879
                                        └──Type expr: Variable: 27879
                                  └──Label type:
                                     └──Type expr: Constructor: id |}]

let%expect_test "poly-3" =
  let str = 
    {|      
      type 'a list = 
        | Nil
        | Cons of 'a * 'a list
      ;;
      
      type pty = { pv : 'a. 'a list };;

      let px = { pv = Nil };;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: list
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: 27884
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 27884
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 27884
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 27884
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: 27884
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 27884
       └──Structure item: Type
          └──Type declaration:
             └──Type name: pty
             └──Type declaration kind: Record
                └──Label declaration:
                   └──Label name: pv
                   └──Label alphas:
                   └──Label betas: 27889
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: 27889
                   └──Type expr: Constructor: pty
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: pty
                   └──Desc: Variable: px
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: pty
                      └──Desc: Record
                         └──Label description:
                            └──Label: pv
                            └──Label argument type:
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: 27898
                            └──Label type:
                               └──Type expr: Constructor: pty
                         └──Expression:
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: 27898
                            └──Desc: Construct
                               └──Constructor description:
                                  └──Name: Nil
                                  └──Constructor type:
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: 27898 |}]

let%expect_test "poly-4" =
  let str = 
    {|
      type 'a list = 
        | Nil
        | Cons of 'a * 'a list
      ;;
      
      type pty = { pv : 'a. 'a list };;

      let px = { pv = Nil };;

      (* match px tests discarded -- reliant on exhaustive pattern matching *)
      let _ = 
        fun pty -> (Cons (true, pty.pv), Cons (1, pty.pv))
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: list
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: 27902
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 27902
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 27902
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 27902
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: 27902
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 27902
       └──Structure item: Type
          └──Type declaration:
             └──Type name: pty
             └──Type declaration kind: Record
                └──Label declaration:
                   └──Label name: pv
                   └──Label alphas:
                   └──Label betas: 27907
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: 27907
                   └──Type expr: Constructor: pty
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: pty
                   └──Desc: Variable: px
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: pty
                      └──Desc: Record
                         └──Label description:
                            └──Label: pv
                            └──Label argument type:
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: 27916
                            └──Label type:
                               └──Type expr: Constructor: pty
                         └──Expression:
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: 27916
                            └──Desc: Construct
                               └──Constructor description:
                                  └──Name: Nil
                                  └──Constructor type:
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: 27916
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: pty
                      └──Type expr: Tuple
                         └──Type expr: Constructor: list
                            └──Type expr: Constructor: bool
                         └──Type expr: Constructor: list
                            └──Type expr: Constructor: int
                   └──Desc: Any
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: pty
                         └──Type expr: Tuple
                            └──Type expr: Constructor: list
                               └──Type expr: Constructor: bool
                            └──Type expr: Constructor: list
                               └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: pty
                            └──Desc: Variable: pty
                         └──Expression:
                            └──Type expr: Tuple
                               └──Type expr: Constructor: list
                                  └──Type expr: Constructor: bool
                               └──Type expr: Constructor: list
                                  └──Type expr: Constructor: int
                            └──Desc: Tuple
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Constructor: bool
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Cons
                                        └──Constructor argument type:
                                           └──Type expr: Tuple
                                              └──Type expr: Constructor: bool
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Constructor: bool
                                        └──Constructor type:
                                           └──Type expr: Constructor: list
                                              └──Type expr: Constructor: bool
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: bool
                                           └──Type expr: Constructor: list
                                              └──Type expr: Constructor: bool
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: bool
                                              └──Desc: Constant: true
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Constructor: bool
                                              └──Desc: Field
                                                 └──Expression:
                                                    └──Type expr: Constructor: pty
                                                    └──Desc: Variable
                                                       └──Variable: pty
                                                 └──Label description:
                                                    └──Label: pv
                                                    └──Label argument type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Constructor: bool
                                                    └──Label type:
                                                       └──Type expr: Constructor: pty
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Constructor: int
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Cons
                                        └──Constructor argument type:
                                           └──Type expr: Tuple
                                              └──Type expr: Constructor: int
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Constructor: int
                                        └──Constructor type:
                                           └──Type expr: Constructor: list
                                              └──Type expr: Constructor: int
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: int
                                           └──Type expr: Constructor: list
                                              └──Type expr: Constructor: int
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Constant: 1
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Constructor: int
                                              └──Desc: Field
                                                 └──Expression:
                                                    └──Type expr: Constructor: pty
                                                    └──Desc: Variable
                                                       └──Variable: pty
                                                 └──Label description:
                                                    └──Label: pv
                                                    └──Label argument type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Constructor: int
                                                    └──Label type:
                                                       └──Type expr: Constructor: pty |}]

let%expect_test "poly-5" =
  let str = 
    {|
      let rec (type 'a) f = 
        fun (x : 'a) -> 1
      and g = 
        fun x -> f x
      ;;

      type 'a perfect_tree = 
        | Leaf of 'a
        | Node of ('a * 'a) perfect_tree
      ;;

      let rec (type 'a) depth = 
        fun (t : 'a perfect_tree) ->
          (match t with 
           ( Leaf _ -> 1
           | Node x -> 1 + depth x
           )
          : int)
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: g
                └──Abstraction:
                   └──Variables: 27978
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 27978
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 27978
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Constant: 1
             └──Value binding:
                └──Variable: f
                └──Abstraction:
                   └──Variables: 27978
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 27978
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 27978
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 27978
                                     └──Type expr: Constructor: int
                                  └──Desc: Variable
                                     └──Variable: f
                               └──Expression:
                                  └──Type expr: Variable: 27978
                                  └──Desc: Variable
                                     └──Variable: x
       └──Structure item: Type
          └──Type declaration:
             └──Type name: perfect_tree
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Leaf
                   └──Constructor alphas: 27967
                   └──Constructor type:
                      └──Type expr: Constructor: perfect_tree
                         └──Type expr: Variable: 27967
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: 27967
                └──Constructor declaration:
                   └──Constructor name: Node
                   └──Constructor alphas: 27967
                   └──Constructor type:
                      └──Type expr: Constructor: perfect_tree
                         └──Type expr: Variable: 27967
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: perfect_tree
                         └──Type expr: Tuple
                            └──Type expr: Variable: 27967
                            └──Type expr: Variable: 27967
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: depth
                └──Abstraction:
                   └──Variables: 27995
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: perfect_tree
                            └──Type expr: Variable: 28013
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: perfect_tree
                               └──Type expr: Variable: 28013
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: perfect_tree
                                     └──Type expr: Variable: 28013
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: perfect_tree
                                  └──Type expr: Variable: 28013
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: perfect_tree
                                           └──Type expr: Variable: 28013
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Leaf
                                              └──Constructor argument type:
                                                 └──Type expr: Variable: 28013
                                              └──Constructor type:
                                                 └──Type expr: Constructor: perfect_tree
                                                    └──Type expr: Variable: 28013
                                           └──Pattern:
                                              └──Type expr: Variable: 28013
                                              └──Desc: Any
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 1
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: perfect_tree
                                           └──Type expr: Variable: 28013
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Node
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: perfect_tree
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 28013
                                                       └──Type expr: Variable: 28013
                                              └──Constructor type:
                                                 └──Type expr: Constructor: perfect_tree
                                                    └──Type expr: Variable: 28013
                                           └──Pattern:
                                              └──Type expr: Constructor: perfect_tree
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 28013
                                                    └──Type expr: Variable: 28013
                                              └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: int
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: int
                                                          └──Type expr: Constructor: int
                                                    └──Desc: Primitive: (+)
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Constant: 1
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: perfect_tree
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 28013
                                                             └──Type expr: Variable: 28013
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: depth
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 28013
                                                          └──Type expr: Variable: 28013
                                                 └──Expression:
                                                    └──Type expr: Constructor: perfect_tree
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 28013
                                                          └──Type expr: Variable: 28013
                                                    └──Desc: Variable
                                                       └──Variable: x |}]

let%expect_test "poly-6" =
  let str = 
    {|  
      type 'a perfect_tree = 
        | Leaf of 'a
        | Node of ('a * 'a) perfect_tree
      ;;

      let rec (type 'a) depth = 
        fun (t : 'a perfect_tree) ->
          (match t with
           ( Leaf _ -> 1
           | Node x -> 1 + d x
           )
          : int)
      and d = 
        fun x -> depth x
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: perfect_tree
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Leaf
                   └──Constructor alphas: 28070
                   └──Constructor type:
                      └──Type expr: Constructor: perfect_tree
                         └──Type expr: Variable: 28070
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: 28070
                └──Constructor declaration:
                   └──Constructor name: Node
                   └──Constructor alphas: 28070
                   └──Constructor type:
                      └──Type expr: Constructor: perfect_tree
                         └──Type expr: Variable: 28070
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: perfect_tree
                         └──Type expr: Tuple
                            └──Type expr: Variable: 28070
                            └──Type expr: Variable: 28070
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: depth
                └──Abstraction:
                   └──Variables: 28080
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: perfect_tree
                            └──Type expr: Variable: 28110
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: perfect_tree
                               └──Type expr: Variable: 28110
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: perfect_tree
                                     └──Type expr: Variable: 28110
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: perfect_tree
                                  └──Type expr: Variable: 28110
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: perfect_tree
                                           └──Type expr: Variable: 28110
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Leaf
                                              └──Constructor argument type:
                                                 └──Type expr: Variable: 28110
                                              └──Constructor type:
                                                 └──Type expr: Constructor: perfect_tree
                                                    └──Type expr: Variable: 28110
                                           └──Pattern:
                                              └──Type expr: Variable: 28110
                                              └──Desc: Any
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 1
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: perfect_tree
                                           └──Type expr: Variable: 28110
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Node
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: perfect_tree
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 28110
                                                       └──Type expr: Variable: 28110
                                              └──Constructor type:
                                                 └──Type expr: Constructor: perfect_tree
                                                    └──Type expr: Variable: 28110
                                           └──Pattern:
                                              └──Type expr: Constructor: perfect_tree
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 28110
                                                    └──Type expr: Variable: 28110
                                              └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: int
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: int
                                                          └──Type expr: Constructor: int
                                                    └──Desc: Primitive: (+)
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Constant: 1
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: perfect_tree
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 28110
                                                             └──Type expr: Variable: 28110
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: d
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 28110
                                                          └──Type expr: Variable: 28110
                                                 └──Expression:
                                                    └──Type expr: Constructor: perfect_tree
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 28110
                                                          └──Type expr: Variable: 28110
                                                    └──Desc: Variable
                                                       └──Variable: x
             └──Value binding:
                └──Variable: d
                └──Abstraction:
                   └──Variables: 28093
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: perfect_tree
                            └──Type expr: Variable: 28093
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: perfect_tree
                               └──Type expr: Variable: 28093
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: perfect_tree
                                        └──Type expr: Variable: 28093
                                     └──Type expr: Constructor: int
                                  └──Desc: Variable
                                     └──Variable: depth
                                     └──Type expr: Variable: 28093
                               └──Expression:
                                  └──Type expr: Constructor: perfect_tree
                                     └──Type expr: Variable: 28093
                                  └──Desc: Variable
                                     └──Variable: x |}]

let%expect_test "poly-8" =
  let str = 
    {|  
      type 'a perfect_tree = 
        | Leaf of 'a
        | Node of ('a * 'a) perfect_tree
      ;;

      let rec (type 'a) depth = 
        fun (t : 'a perfect_tree) ->
          (match t with 
           ( Leaf x -> x
           | Node x -> 1 + depth x
           )
          : int)
      ;; 
    |}
  in
  print_infer_result str;
  [%expect {|
    ("Cannot unify types"
     ("Type_expr.decode type_expr1" (Type 28207 (Former (Constr () int))))
     ("Type_expr.decode type_expr2" (Type 28204 (Var 28204)))) |}]

let%expect_test "poly-9" =
  let str = 
    {|  
      type 'a perfect_tree = 
        | Leaf of 'a
        | Node of ('a * 'a) perfect_tree
      ;;

      let rec (type 'a) depth = 
        exists (type 'b) ->
        fun (t : 'a perfect_tree) ->
          (match t with
           ( Leaf x -> x
           | Node x -> depth x
           )
          : 'b)
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    ("Cannot unify types"
     ("Type_expr.decode type_expr1"
      (Type 28241 (Former (Constr ((Type 28224 (Var 28224))) perfect_tree))))
     ("Type_expr.decode type_expr2"
      (Type 28244
       (Former
        (Constr
         ((Type 28245
           (Former (Tuple ((Type 28234 (Var 28234)) (Type 28234 (Var 28234)))))))
         perfect_tree))))) |}]

let%expect_test "poly-10" =
  let str = 
    {|
      type 'a perfect_tree = 
        | Leaf of 'a
        | Node of ('a * 'a) perfect_tree
      ;;

      let rec (type 'a 'b) depth = 
        fun (t : 'a perfect_tree) ->
          (match t with
          ( Leaf x -> x
          | Node x -> depth x
          )
          : 'b)
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    ("Cannot unify types"
     ("Type_expr.decode type_expr1" (Type 28284 (Var 28284)))
     ("Type_expr.decode type_expr2" (Type 28279 (Var 28279)))) |}]

let%expect_test "poly-11" =
  let str = 
    {|
      external not : bool -> bool = "%not";;

      let rec (type 'a) id = 
        fun (x : 'a) -> (x : 'a)
      and neg = 
        fun i b -> (id (0 - i), id (not b))
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Primitive
          └──Value description:
             └──Name: not
             └──Scheme:
                └──Variables:
                └──Type expr: Arrow
                   └──Type expr: Constructor: bool
                   └──Type expr: Constructor: bool
             └──Primitive name: %not
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: id
                └──Abstraction:
                   └──Variables: 28293
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 28351
                         └──Type expr: Variable: 28351
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 28351
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: 28351
                            └──Desc: Variable
                               └──Variable: x
             └──Value binding:
                └──Variable: neg
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Constructor: bool
                            └──Type expr: Tuple
                               └──Type expr: Constructor: int
                               └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: i
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: bool
                               └──Type expr: Tuple
                                  └──Type expr: Constructor: int
                                  └──Type expr: Constructor: bool
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: bool
                                  └──Desc: Variable: b
                               └──Expression:
                                  └──Type expr: Tuple
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: bool
                                  └──Desc: Tuple
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: id
                                                 └──Type expr: Constructor: int
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: int
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: int
                                                                └──Type expr: Constructor: int
                                                          └──Desc: Primitive: (-)
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Constant: 0
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: i
                                     └──Expression:
                                        └──Type expr: Constructor: bool
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: bool
                                                 └──Type expr: Constructor: bool
                                              └──Desc: Variable
                                                 └──Variable: id
                                                 └──Type expr: Constructor: bool
                                           └──Expression:
                                              └──Type expr: Constructor: bool
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: bool
                                                       └──Type expr: Constructor: bool
                                                    └──Desc: Variable
                                                       └──Variable: not
                                                 └──Expression:
                                                    └──Type expr: Constructor: bool
                                                    └──Desc: Variable
                                                       └──Variable: b |}]