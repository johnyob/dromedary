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
  [%expect
    {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: t
             └──Type declaration kind: Record
                └──Label declaration:
                   └──Label name: t
                   └──Label alphas: 295
                   └──Label betas:
                   └──Type expr: Variable: 295
                   └──Type expr: Constructor: t
                      └──Type expr: Variable: 295
       └──Structure item: Type
          └──Type declaration:
             └──Type name: fold
             └──Type declaration kind: Record
                └──Label declaration:
                   └──Label name: fold
                   └──Label alphas: 297
                   └──Label betas: 298
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: 298
                         └──Type expr: Arrow
                            └──Type expr: Variable: 297
                            └──Type expr: Variable: 298
                      └──Type expr: Arrow
                         └──Type expr: Variable: 298
                         └──Type expr: Variable: 298
                   └──Type expr: Constructor: fold
                      └──Type expr: Variable: 297
       └──Structure item: Type
          └──Type declaration:
             └──Type name: list
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: 304
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 304
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 304
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 304
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: 304
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 304
       └──Structure item: Primitive
          └──Value description:
             └──Name: fold_left
             └──Scheme:
                └──Variables: 1,0
                └──Type expr: Arrow
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: 0
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: 1
                         └──Type expr: Arrow
                            └──Type expr: Variable: 0
                            └──Type expr: Variable: 1
                      └──Type expr: Arrow
                         └──Type expr: Variable: 1
                         └──Type expr: Variable: 1
             └──Primitive name: %fold_left
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 19
                      └──Type expr: Constructor: fold
                         └──Type expr: Variable: 19
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 19
                         └──Type expr: Constructor: fold
                            └──Type expr: Variable: 19
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: 19
                            └──Desc: Variable: xs
                         └──Expression:
                            └──Type expr: Constructor: fold
                               └──Type expr: Variable: 19
                            └──Desc: Record
                               └──Label description:
                                  └──Label: fold
                                  └──Label argument type:
                                     └──Type expr: Arrow
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: 27
                                           └──Type expr: Arrow
                                              └──Type expr: Variable: 19
                                              └──Type expr: Variable: 27
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: 27
                                           └──Type expr: Variable: 27
                                  └──Label type:
                                     └──Type expr: Constructor: fold
                                        └──Type expr: Variable: 19
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: 27
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: 19
                                           └──Type expr: Variable: 27
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: 27
                                        └──Type expr: Variable: 27
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: 19
                                           └──Type expr: Arrow
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: 27
                                                 └──Type expr: Arrow
                                                    └──Type expr: Variable: 19
                                                    └──Type expr: Variable: 27
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: 27
                                                 └──Type expr: Variable: 27
                                        └──Desc: Variable
                                           └──Variable: fold_left
                                           └──Type expr: Variable: 27
                                           └──Type expr: Variable: 19
                                     └──Expression:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Variable: 19
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
  [%expect
    {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: id
             └──Type declaration kind: Record
                └──Label declaration:
                   └──Label name: id
                   └──Label alphas:
                   └──Label betas: 144
                   └──Type expr: Arrow
                      └──Type expr: Variable: 144
                      └──Type expr: Variable: 144
                   └──Type expr: Constructor: id
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 2
                      └──Type expr: Variable: 2
                   └──Desc: Variable: id
                └──Abstraction:
                   └──Variables: 2,2
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 2
                         └──Type expr: Variable: 2
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 2
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: 2
                            └──Desc: Variable
                               └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 22
                      └──Type expr: Variable: 22
                   └──Desc: Variable: id
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 22
                         └──Type expr: Variable: 22
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
                                                       └──Type expr: Variable: 15
                                                       └──Type expr: Variable: 15
                                                 └──Label type:
                                                    └──Type expr: Constructor: id
                                              └──Expression:
                                                 └──Type expr: Arrow
                                                    └──Type expr: Variable: 15
                                                    └──Type expr: Variable: 15
                                                 └──Desc: Variable
                                                    └──Variable: id
                                                    └──Type expr: Variable: 15
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: 22
                               └──Type expr: Variable: 22
                            └──Desc: Field
                               └──Expression:
                                  └──Type expr: Constructor: id
                                  └──Desc: Variable
                                     └──Variable: boxed_id
                               └──Label description:
                                  └──Label: id
                                  └──Label argument type:
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: 22
                                        └──Type expr: Variable: 22
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
  [%expect
    {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: list
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: 27
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 27
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 27
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 27
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: 27
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 27
       └──Structure item: Type
          └──Type declaration:
             └──Type name: pty
             └──Type declaration kind: Record
                └──Label declaration:
                   └──Label name: pv
                   └──Label alphas:
                   └──Label betas: 32
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: 32
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
                                  └──Type expr: Variable: 6
                            └──Label type:
                               └──Type expr: Constructor: pty
                         └──Expression:
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: 6
                            └──Desc: Construct
                               └──Constructor description:
                                  └──Name: Nil
                                  └──Constructor type:
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: 6 |}]


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
  [%expect
    {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: list
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: 10
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 10
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 10
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 10
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: 10
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 10
       └──Structure item: Type
          └──Type declaration:
             └──Type name: pty
             └──Type declaration kind: Record
                └──Label declaration:
                   └──Label name: pv
                   └──Label alphas:
                   └──Label betas: 15
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: 15
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
                                  └──Type expr: Variable: 6
                            └──Label type:
                               └──Type expr: Constructor: pty
                         └──Expression:
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: 6
                            └──Desc: Construct
                               └──Constructor description:
                                  └──Name: Nil
                                  └──Constructor type:
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: 6
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
  [%expect
    {|
    Structure:
    └──Structure:
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: g
                └──Abstraction:
                   └──Variables: 6
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 6
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 6
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Constant: 1
             └──Value binding:
                └──Variable: f
                └──Abstraction:
                   └──Variables: 6
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 6
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 6
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 6
                                     └──Type expr: Constructor: int
                                  └──Desc: Variable
                                     └──Variable: f
                               └──Expression:
                                  └──Type expr: Variable: 6
                                  └──Desc: Variable
                                     └──Variable: x
       └──Structure item: Type
          └──Type declaration:
             └──Type name: perfect_tree
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Leaf
                   └──Constructor alphas: 57
                   └──Constructor type:
                      └──Type expr: Constructor: perfect_tree
                         └──Type expr: Variable: 57
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: 57
                └──Constructor declaration:
                   └──Constructor name: Node
                   └──Constructor alphas: 57
                   └──Constructor type:
                      └──Type expr: Constructor: perfect_tree
                         └──Type expr: Variable: 57
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: perfect_tree
                         └──Type expr: Tuple
                            └──Type expr: Variable: 57
                            └──Type expr: Variable: 57
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: depth
                └──Abstraction:
                   └──Variables: 23
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: perfect_tree
                            └──Type expr: Variable: 41
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: perfect_tree
                               └──Type expr: Variable: 41
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: perfect_tree
                                     └──Type expr: Variable: 41
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: perfect_tree
                                  └──Type expr: Variable: 41
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: perfect_tree
                                           └──Type expr: Variable: 41
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Leaf
                                              └──Constructor argument type:
                                                 └──Type expr: Variable: 41
                                              └──Constructor type:
                                                 └──Type expr: Constructor: perfect_tree
                                                    └──Type expr: Variable: 41
                                           └──Pattern:
                                              └──Type expr: Variable: 41
                                              └──Desc: Any
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 1
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: perfect_tree
                                           └──Type expr: Variable: 41
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Node
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: perfect_tree
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 41
                                                       └──Type expr: Variable: 41
                                              └──Constructor type:
                                                 └──Type expr: Constructor: perfect_tree
                                                    └──Type expr: Variable: 41
                                           └──Pattern:
                                              └──Type expr: Constructor: perfect_tree
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 41
                                                    └──Type expr: Variable: 41
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
                                                             └──Type expr: Variable: 41
                                                             └──Type expr: Variable: 41
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: depth
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 41
                                                          └──Type expr: Variable: 41
                                                 └──Expression:
                                                    └──Type expr: Constructor: perfect_tree
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 41
                                                          └──Type expr: Variable: 41
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
  [%expect
    {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: perfect_tree
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Leaf
                   └──Constructor alphas: 98
                   └──Constructor type:
                      └──Type expr: Constructor: perfect_tree
                         └──Type expr: Variable: 98
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: 98
                └──Constructor declaration:
                   └──Constructor name: Node
                   └──Constructor alphas: 98
                   └──Constructor type:
                      └──Type expr: Constructor: perfect_tree
                         └──Type expr: Variable: 98
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: perfect_tree
                         └──Type expr: Tuple
                            └──Type expr: Variable: 98
                            └──Type expr: Variable: 98
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: depth
                └──Abstraction:
                   └──Variables: 5
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: perfect_tree
                            └──Type expr: Variable: 35
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: perfect_tree
                               └──Type expr: Variable: 35
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: perfect_tree
                                     └──Type expr: Variable: 35
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: perfect_tree
                                  └──Type expr: Variable: 35
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: perfect_tree
                                           └──Type expr: Variable: 35
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Leaf
                                              └──Constructor argument type:
                                                 └──Type expr: Variable: 35
                                              └──Constructor type:
                                                 └──Type expr: Constructor: perfect_tree
                                                    └──Type expr: Variable: 35
                                           └──Pattern:
                                              └──Type expr: Variable: 35
                                              └──Desc: Any
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 1
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: perfect_tree
                                           └──Type expr: Variable: 35
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Node
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: perfect_tree
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 35
                                                       └──Type expr: Variable: 35
                                              └──Constructor type:
                                                 └──Type expr: Constructor: perfect_tree
                                                    └──Type expr: Variable: 35
                                           └──Pattern:
                                              └──Type expr: Constructor: perfect_tree
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 35
                                                    └──Type expr: Variable: 35
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
                                                             └──Type expr: Variable: 35
                                                             └──Type expr: Variable: 35
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: d
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 35
                                                          └──Type expr: Variable: 35
                                                 └──Expression:
                                                    └──Type expr: Constructor: perfect_tree
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 35
                                                          └──Type expr: Variable: 35
                                                    └──Desc: Variable
                                                       └──Variable: x
             └──Value binding:
                └──Variable: d
                └──Abstraction:
                   └──Variables: 18
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: perfect_tree
                            └──Type expr: Variable: 18
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: perfect_tree
                               └──Type expr: Variable: 18
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: perfect_tree
                                        └──Type expr: Variable: 18
                                     └──Type expr: Constructor: int
                                  └──Desc: Variable
                                     └──Variable: depth
                                     └──Type expr: Variable: 18
                               └──Expression:
                                  └──Type expr: Constructor: perfect_tree
                                     └──Type expr: Variable: 18
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
  [%expect
    {|
    ("Cannot unify types"
     ("Type_expr.decode type_expr1" (Type 35 (Former (Constr () int))))
     ("Type_expr.decode type_expr2" (Type 32 (Var 32)))) |}]


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
  [%expect
    {|
    ("Cannot unify types"
     ("Type_expr.decode type_expr1"
      (Type 25 (Former (Constr ((Type 8 (Var 8))) perfect_tree))))
     ("Type_expr.decode type_expr2"
      (Type 28
       (Former
        (Constr
         ((Type 29 (Former (Tuple ((Type 18 (Var 18)) (Type 18 (Var 18)))))))
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
  [%expect
    {|
    ("Cannot unify types" ("Type_expr.decode type_expr1" (Type 33 (Var 33)))
     ("Type_expr.decode type_expr2" (Type 28 (Var 28)))) |}]


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
  [%expect
    {|
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
                   └──Variables: 8
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 66
                         └──Type expr: Variable: 66
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 66
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: 66
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
