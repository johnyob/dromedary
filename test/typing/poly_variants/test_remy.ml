open! Import
open Util

(* Example from the appendix of https://www.cs.tufts.edu/~nr/cs257/archive/didier-remy/type-checking-records.pdf *)

let%expect_test "" =
  let str = 
    {|
      external failwith : 'a. string -> 'a = "%failwith";;

      let rec select = fun t1 f -> 
        match t1 with
        ( `Nil -> failwith "select"
        | `Cons (x, t2) ->
            if f x then (x, t2) 
            else 
              let (y, t3) = select t2 f 
              in (y, `Cons (x, t3)) 
        )
      ;;

      let rec fold_right = fun t init f ->
        match t with
        ( `Nil -> init
        | `Cons (x, t) -> f x (fold_right t init f)
        )
      ;;

      
      let partition = fun t f ->
        fold_right t (`Nil, `Nil)
          (fun x (l, r) -> 
            if f x then (`Cons (x, l), r) else (l, `Cons (x, r)) )
      ;;

      let id = fun x -> x;;
      let compose = fun f g x -> f (g x);;

      let cons = fun x t -> `Cons (x, t);;

      let sort_append = fun f le ->
        let rec loop = fun t ->
          match t with
          ( `Nil -> id
          | `Cons (_, _) -> 
            let (pivot, t) = select t f in
            let (l, r) = partition t (fun y -> le y pivot) in
            compose (loop l) (compose (cons pivot) (loop r))
          )
        in loop
      ;;

      let sort = fun t le ->
        sort_append (fun x -> true) le t `Nil
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Primitive
          └──Value description:
             └──Name: failwith
             └──Scheme:
                └──Variables: a11798
                └──Type expr: Arrow
                   └──Type expr: Constructor: string
                   └──Type expr: Variable: a11798
             └──Primitive name: %failwith
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: select
                └──Abstraction:
                   └──Variables: a11884
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Mu
                            └──Variable: a11885
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Cons
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: a11884
                                        └──Type expr: Variable: a11885
                                  └──Type expr: Row cons
                                     └──Label: Nil
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: a11884
                               └──Type expr: Constructor: bool
                            └──Type expr: Tuple
                               └──Type expr: Variable: a11884
                               └──Type expr: Mu
                                  └──Variable: a11885
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a11884
                                              └──Type expr: Variable: a11885
                                        └──Type expr: Row cons
                                           └──Label: Nil
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Mu
                               └──Variable: a11885
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a11884
                                           └──Type expr: Variable: a11885
                                     └──Type expr: Row cons
                                        └──Label: Nil
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a11884
                                  └──Type expr: Constructor: bool
                               └──Type expr: Tuple
                                  └──Type expr: Variable: a11884
                                  └──Type expr: Mu
                                     └──Variable: a11885
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a11884
                                                 └──Type expr: Variable: a11885
                                           └──Type expr: Row cons
                                              └──Label: Nil
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a11884
                                     └──Type expr: Constructor: bool
                                  └──Desc: Variable: f
                               └──Expression:
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: a11884
                                     └──Type expr: Mu
                                        └──Variable: a11885
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a11884
                                                    └──Type expr: Variable: a11885
                                              └──Type expr: Row cons
                                                 └──Label: Nil
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Mu
                                           └──Variable: a11885
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Cons
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a11884
                                                       └──Type expr: Variable: a11885
                                                 └──Type expr: Row cons
                                                    └──Label: Nil
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                        └──Desc: Variable
                                           └──Variable: t1
                                     └──Type expr: Mu
                                        └──Variable: a11885
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a11884
                                                    └──Type expr: Variable: a11885
                                              └──Type expr: Row cons
                                                 └──Label: Nil
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Nil
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Mu
                                                             └──Variable: a11817
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a11884
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Variable: a11817
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                                       └──Type expr: Row uniform
                                                          └──Type expr: Constructor: absent
                                              └──Desc: Variant
                                                 └──Variant description:
                                                    └──Tag: Nil
                                                    └──Variant row:
                                                       └──Type expr: Row cons
                                                          └──Label: Nil
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Mu
                                                                   └──Variable: a11817
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a11884
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Variable: a11817
                                                                            └──Type expr: Row cons
                                                                               └──Label: Nil
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row uniform
                                                                                  └──Type expr: Constructor: absent
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a11884
                                                 └──Type expr: Mu
                                                    └──Variable: a11885
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a11884
                                                                └──Type expr: Variable: a11885
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: string
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a11884
                                                          └──Type expr: Mu
                                                             └──Variable: a11885
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a11884
                                                                         └──Type expr: Variable: a11885
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                    └──Desc: Variable
                                                       └──Variable: failwith
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a11884
                                                          └──Type expr: Mu
                                                             └──Variable: a11885
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a11884
                                                                         └──Type expr: Variable: a11885
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                 └──Expression:
                                                    └──Type expr: Constructor: string
                                                    └──Desc: Constant: select
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Nil
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Mu
                                                             └──Variable: a11817
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a11884
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Variable: a11817
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                                       └──Type expr: Row uniform
                                                          └──Type expr: Constructor: absent
                                              └──Desc: Variant
                                                 └──Variant description:
                                                    └──Tag: Cons
                                                    └──Variant row:
                                                       └──Type expr: Row cons
                                                          └──Label: Nil
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Mu
                                                                   └──Variable: a11817
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a11884
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Variable: a11817
                                                                            └──Type expr: Row cons
                                                                               └──Label: Nil
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row uniform
                                                                                  └──Type expr: Constructor: absent
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                                 └──Pattern:
                                                    └──Type expr: Mu
                                                       └──Variable: a11817
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a11884
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Variable: a11817
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Variable: a11884
                                                          └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Mu
                                                             └──Variable: a11885
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a11884
                                                                         └──Type expr: Variable: a11885
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                          └──Desc: Variable: t2
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a11884
                                                 └──Type expr: Mu
                                                    └──Variable: a11885
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a11884
                                                                └──Type expr: Variable: a11885
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                              └──Desc: If
                                                 └──Expression:
                                                    └──Type expr: Constructor: bool
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a11884
                                                             └──Type expr: Constructor: bool
                                                          └──Desc: Variable
                                                             └──Variable: f
                                                       └──Expression:
                                                          └──Type expr: Variable: a11884
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a11884
                                                       └──Type expr: Mu
                                                          └──Variable: a11885
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a11884
                                                                      └──Type expr: Variable: a11885
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Variable: a11884
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Mu
                                                             └──Variable: a11885
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a11884
                                                                         └──Type expr: Variable: a11885
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                          └──Desc: Variable
                                                             └──Variable: t2
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a11884
                                                       └──Type expr: Mu
                                                          └──Variable: a11885
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a11884
                                                                      └──Type expr: Variable: a11885
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                    └──Desc: Let
                                                       └──Value bindings:
                                                          └──Value binding:
                                                             └──Pattern:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a11884
                                                                   └──Type expr: Mu
                                                                      └──Variable: a11885
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: a11884
                                                                                  └──Type expr: Variable: a11885
                                                                            └──Type expr: Row cons
                                                                               └──Label: Nil
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row uniform
                                                                                  └──Type expr: Constructor: absent
                                                                └──Desc: Tuple
                                                                   └──Pattern:
                                                                      └──Type expr: Variable: a11884
                                                                      └──Desc: Variable: y
                                                                   └──Pattern:
                                                                      └──Type expr: Mu
                                                                         └──Variable: a11885
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a11884
                                                                                     └──Type expr: Variable: a11885
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row uniform
                                                                                     └──Type expr: Constructor: absent
                                                                      └──Desc: Variable: t3
                                                             └──Abstraction:
                                                                └──Variables:
                                                                └──Expression:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a11884
                                                                      └──Type expr: Mu
                                                                         └──Variable: a11885
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a11884
                                                                                     └──Type expr: Variable: a11885
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row uniform
                                                                                     └──Type expr: Constructor: absent
                                                                   └──Desc: Application
                                                                      └──Expression:
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Variable: a11884
                                                                               └──Type expr: Constructor: bool
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a11884
                                                                               └──Type expr: Mu
                                                                                  └──Variable: a11885
                                                                                  └──Type expr: Variant
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Cons
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Variable: a11884
                                                                                              └──Type expr: Variable: a11885
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Nil
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Constructor: unit
                                                                                           └──Type expr: Row uniform
                                                                                              └──Type expr: Constructor: absent
                                                                         └──Desc: Application
                                                                            └──Expression:
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Mu
                                                                                     └──Variable: a11885
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Variable: a11884
                                                                                                 └──Type expr: Variable: a11885
                                                                                           └──Type expr: Row cons
                                                                                              └──Label: Nil
                                                                                              └──Type expr: Constructor: present
                                                                                                 └──Type expr: Constructor: unit
                                                                                              └──Type expr: Row uniform
                                                                                                 └──Type expr: Constructor: absent
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Variable: a11884
                                                                                        └──Type expr: Constructor: bool
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Variable: a11884
                                                                                        └──Type expr: Mu
                                                                                           └──Variable: a11885
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: a11884
                                                                                                       └──Type expr: Variable: a11885
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Nil
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Constructor: unit
                                                                                                    └──Type expr: Row uniform
                                                                                                       └──Type expr: Constructor: absent
                                                                               └──Desc: Variable
                                                                                  └──Variable: select
                                                                            └──Expression:
                                                                               └──Type expr: Mu
                                                                                  └──Variable: a11885
                                                                                  └──Type expr: Variant
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Cons
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Variable: a11884
                                                                                              └──Type expr: Variable: a11885
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Nil
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Constructor: unit
                                                                                           └──Type expr: Row uniform
                                                                                              └──Type expr: Constructor: absent
                                                                               └──Desc: Variable
                                                                                  └──Variable: t2
                                                                      └──Expression:
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Variable: a11884
                                                                            └──Type expr: Constructor: bool
                                                                         └──Desc: Variable
                                                                            └──Variable: f
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a11884
                                                             └──Type expr: Mu
                                                                └──Variable: a11885
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a11884
                                                                            └──Type expr: Variable: a11885
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Variable: a11884
                                                                └──Desc: Variable
                                                                   └──Variable: y
                                                             └──Expression:
                                                                └──Type expr: Mu
                                                                   └──Variable: a11885
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a11884
                                                                               └──Type expr: Variable: a11885
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row uniform
                                                                               └──Type expr: Constructor: absent
                                                                └──Desc: Variant
                                                                   └──Variant description:
                                                                      └──Tag: Cons
                                                                      └──Variant row:
                                                                         └──Type expr: Mu
                                                                            └──Variable: a11824
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a11884
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Variable: a11824
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row uniform
                                                                                     └──Type expr: Constructor: absent
                                                                   └──Expression:
                                                                      └──Type expr: Mu
                                                                         └──Variable: a11817
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a11884
                                                                            └──Type expr: Variant
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Cons
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Variable: a11817
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Nil
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Row uniform
                                                                                        └──Type expr: Constructor: absent
                                                                      └──Desc: Tuple
                                                                         └──Expression:
                                                                            └──Type expr: Variable: a11884
                                                                            └──Desc: Variable
                                                                               └──Variable: x
                                                                         └──Expression:
                                                                            └──Type expr: Mu
                                                                               └──Variable: a11885
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: a11884
                                                                                           └──Type expr: Variable: a11885
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Nil
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Constructor: unit
                                                                                        └──Type expr: Row uniform
                                                                                           └──Type expr: Constructor: absent
                                                                            └──Desc: Variable
                                                                               └──Variable: t3
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: fold_right
                └──Abstraction:
                   └──Variables: a11943,a11946
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Mu
                            └──Variable: a11955
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Nil
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a11946
                                           └──Type expr: Variable: a11955
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                         └──Type expr: Arrow
                            └──Type expr: Variable: a11943
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a11946
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a11943
                                     └──Type expr: Variable: a11943
                               └──Type expr: Variable: a11943
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Mu
                               └──Variable: a11955
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Nil
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a11946
                                              └──Type expr: Variable: a11955
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a11943
                               └──Type expr: Arrow
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a11946
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: a11943
                                        └──Type expr: Variable: a11943
                                  └──Type expr: Variable: a11943
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: a11943
                                  └──Desc: Variable: init
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: a11946
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: a11943
                                           └──Type expr: Variable: a11943
                                     └──Type expr: Variable: a11943
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: a11946
                                           └──Type expr: Arrow
                                              └──Type expr: Variable: a11943
                                              └──Type expr: Variable: a11943
                                        └──Desc: Variable: f
                                     └──Expression:
                                        └──Type expr: Variable: a11943
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Mu
                                                 └──Variable: a11955
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Nil
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a11946
                                                                └──Type expr: Variable: a11955
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                              └──Desc: Variable
                                                 └──Variable: t
                                           └──Type expr: Mu
                                              └──Variable: a11955
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Nil
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a11946
                                                             └──Type expr: Variable: a11955
                                                       └──Type expr: Row uniform
                                                          └──Type expr: Constructor: absent
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Nil
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Mu
                                                                   └──Variable: a11915
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a11946
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Variable: a11915
                                                                               └──Type expr: Row uniform
                                                                                  └──Type expr: Constructor: absent
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                                    └──Desc: Variant
                                                       └──Variant description:
                                                          └──Tag: Nil
                                                          └──Variant row:
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Mu
                                                                         └──Variable: a11915
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a11946
                                                                            └──Type expr: Variant
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Variable: a11915
                                                                                     └──Type expr: Row uniform
                                                                                        └──Type expr: Constructor: absent
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                 └──Expression:
                                                    └──Type expr: Variable: a11943
                                                    └──Desc: Variable
                                                       └──Variable: init
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Nil
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Mu
                                                                   └──Variable: a11915
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a11946
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Variable: a11915
                                                                               └──Type expr: Row uniform
                                                                                  └──Type expr: Constructor: absent
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                                    └──Desc: Variant
                                                       └──Variant description:
                                                          └──Tag: Cons
                                                          └──Variant row:
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Mu
                                                                         └──Variable: a11915
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a11946
                                                                            └──Type expr: Variant
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Variable: a11915
                                                                                     └──Type expr: Row uniform
                                                                                        └──Type expr: Constructor: absent
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                       └──Pattern:
                                                          └──Type expr: Mu
                                                             └──Variable: a11915
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a11946
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Variable: a11915
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Variable: a11946
                                                                └──Desc: Variable: x
                                                             └──Pattern:
                                                                └──Type expr: Mu
                                                                   └──Variable: a11955
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: a11946
                                                                                  └──Type expr: Variable: a11955
                                                                            └──Type expr: Row uniform
                                                                               └──Type expr: Constructor: absent
                                                                └──Desc: Variable: t
                                                 └──Expression:
                                                    └──Type expr: Variable: a11943
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a11943
                                                             └──Type expr: Variable: a11943
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: a11946
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: a11943
                                                                      └──Type expr: Variable: a11943
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Variable: a11946
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Variable: a11943
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: a11946
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: a11943
                                                                         └──Type expr: Variable: a11943
                                                                   └──Type expr: Variable: a11943
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: a11943
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Variable: a11946
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Variable: a11943
                                                                                  └──Type expr: Variable: a11943
                                                                            └──Type expr: Variable: a11943
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Mu
                                                                                  └──Variable: a11955
                                                                                  └──Type expr: Variant
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Nil
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Constructor: unit
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Variable: a11946
                                                                                                 └──Type expr: Variable: a11955
                                                                                           └──Type expr: Row uniform
                                                                                              └──Type expr: Constructor: absent
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Variable: a11943
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Variable: a11946
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Variable: a11943
                                                                                           └──Type expr: Variable: a11943
                                                                                     └──Type expr: Variable: a11943
                                                                            └──Desc: Variable
                                                                               └──Variable: fold_right
                                                                         └──Expression:
                                                                            └──Type expr: Mu
                                                                               └──Variable: a11955
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Nil
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Cons
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Variable: a11946
                                                                                              └──Type expr: Variable: a11955
                                                                                        └──Type expr: Row uniform
                                                                                           └──Type expr: Constructor: absent
                                                                            └──Desc: Variable
                                                                               └──Variable: t
                                                                   └──Expression:
                                                                      └──Type expr: Variable: a11943
                                                                      └──Desc: Variable
                                                                         └──Variable: init
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: a11946
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: a11943
                                                                      └──Type expr: Variable: a11943
                                                                └──Desc: Variable
                                                                   └──Variable: f
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Mu
                         └──Variable: a11977
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Nil
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Row cons
                                  └──Label: Cons
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: a12070
                                        └──Type expr: Variable: a11977
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: a12070
                            └──Type expr: Constructor: bool
                         └──Type expr: Tuple
                            └──Type expr: Mu
                               └──Variable: a12051
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a12070
                                           └──Type expr: Variable: a12051
                                     └──Type expr: Row cons
                                        └──Label: Nil
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Variable: a12056
                            └──Type expr: Mu
                               └──Variable: a12071
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a12070
                                           └──Type expr: Variable: a12071
                                     └──Type expr: Row cons
                                        └──Label: Nil
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Variable: a12076
                   └──Desc: Variable: partition
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Mu
                            └──Variable: a11977
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Nil
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a12070
                                           └──Type expr: Variable: a11977
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: a12070
                               └──Type expr: Constructor: bool
                            └──Type expr: Tuple
                               └──Type expr: Mu
                                  └──Variable: a12051
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a12070
                                              └──Type expr: Variable: a12051
                                        └──Type expr: Row cons
                                           └──Label: Nil
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: a12056
                               └──Type expr: Mu
                                  └──Variable: a12071
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a12070
                                              └──Type expr: Variable: a12071
                                        └──Type expr: Row cons
                                           └──Label: Nil
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: a12076
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Mu
                               └──Variable: a11977
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Nil
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a12070
                                              └──Type expr: Variable: a11977
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a12070
                                  └──Type expr: Constructor: bool
                               └──Type expr: Tuple
                                  └──Type expr: Mu
                                     └──Variable: a12051
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a12070
                                                 └──Type expr: Variable: a12051
                                           └──Type expr: Row cons
                                              └──Label: Nil
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Variable: a12056
                                  └──Type expr: Mu
                                     └──Variable: a12071
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a12070
                                                 └──Type expr: Variable: a12071
                                           └──Type expr: Row cons
                                              └──Label: Nil
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Variable: a12076
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a12070
                                     └──Type expr: Constructor: bool
                                  └──Desc: Variable: f
                               └──Expression:
                                  └──Type expr: Tuple
                                     └──Type expr: Mu
                                        └──Variable: a12051
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a12070
                                                    └──Type expr: Variable: a12051
                                              └──Type expr: Row cons
                                                 └──Label: Nil
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Variable: a12056
                                     └──Type expr: Mu
                                        └──Variable: a12071
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a12070
                                                    └──Type expr: Variable: a12071
                                              └──Type expr: Row cons
                                                 └──Label: Nil
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Variable: a12076
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Variable: a12070
                                              └──Type expr: Arrow
                                                 └──Type expr: Tuple
                                                    └──Type expr: Mu
                                                       └──Variable: a12051
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a12070
                                                                   └──Type expr: Variable: a12051
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a12056
                                                    └──Type expr: Mu
                                                       └──Variable: a12071
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a12070
                                                                   └──Type expr: Variable: a12071
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a12076
                                                 └──Type expr: Tuple
                                                    └──Type expr: Mu
                                                       └──Variable: a12051
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a12070
                                                                   └──Type expr: Variable: a12051
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a12056
                                                    └──Type expr: Mu
                                                       └──Variable: a12071
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a12070
                                                                   └──Type expr: Variable: a12071
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a12076
                                           └──Type expr: Tuple
                                              └──Type expr: Mu
                                                 └──Variable: a12051
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a12070
                                                             └──Type expr: Variable: a12051
                                                       └──Type expr: Row cons
                                                          └──Label: Nil
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Variable: a12056
                                              └──Type expr: Mu
                                                 └──Variable: a12071
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a12070
                                                             └──Type expr: Variable: a12071
                                                       └──Type expr: Row cons
                                                          └──Label: Nil
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Variable: a12076
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Tuple
                                                    └──Type expr: Mu
                                                       └──Variable: a12051
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a12070
                                                                   └──Type expr: Variable: a12051
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a12056
                                                    └──Type expr: Mu
                                                       └──Variable: a12071
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a12070
                                                                   └──Type expr: Variable: a12071
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a12076
                                                 └──Type expr: Arrow
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: a12070
                                                       └──Type expr: Arrow
                                                          └──Type expr: Tuple
                                                             └──Type expr: Mu
                                                                └──Variable: a12051
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a12070
                                                                            └──Type expr: Variable: a12051
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a12056
                                                             └──Type expr: Mu
                                                                └──Variable: a12071
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a12070
                                                                            └──Type expr: Variable: a12071
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a12076
                                                          └──Type expr: Tuple
                                                             └──Type expr: Mu
                                                                └──Variable: a12051
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a12070
                                                                            └──Type expr: Variable: a12051
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a12056
                                                             └──Type expr: Mu
                                                                └──Variable: a12071
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a12070
                                                                            └──Type expr: Variable: a12071
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a12076
                                                    └──Type expr: Tuple
                                                       └──Type expr: Mu
                                                          └──Variable: a12051
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a12070
                                                                      └──Type expr: Variable: a12051
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: a12056
                                                       └──Type expr: Mu
                                                          └──Variable: a12071
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a12070
                                                                      └──Type expr: Variable: a12071
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: a12076
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Mu
                                                          └──Variable: a11977
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a12070
                                                                         └──Type expr: Variable: a11977
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                       └──Type expr: Arrow
                                                          └──Type expr: Tuple
                                                             └──Type expr: Mu
                                                                └──Variable: a12051
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a12070
                                                                            └──Type expr: Variable: a12051
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a12056
                                                             └──Type expr: Mu
                                                                └──Variable: a12071
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a12070
                                                                            └──Type expr: Variable: a12071
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a12076
                                                          └──Type expr: Arrow
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a12070
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Mu
                                                                         └──Variable: a12051
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a12070
                                                                                     └──Type expr: Variable: a12051
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: a12056
                                                                      └──Type expr: Mu
                                                                         └──Variable: a12071
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a12070
                                                                                     └──Type expr: Variable: a12071
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: a12076
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Mu
                                                                         └──Variable: a12051
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a12070
                                                                                     └──Type expr: Variable: a12051
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: a12056
                                                                      └──Type expr: Mu
                                                                         └──Variable: a12071
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a12070
                                                                                     └──Type expr: Variable: a12071
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: a12076
                                                             └──Type expr: Tuple
                                                                └──Type expr: Mu
                                                                   └──Variable: a12051
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a12070
                                                                               └──Type expr: Variable: a12051
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: a12056
                                                                └──Type expr: Mu
                                                                   └──Variable: a12071
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a12070
                                                                               └──Type expr: Variable: a12071
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: a12076
                                                    └──Desc: Variable
                                                       └──Variable: fold_right
                                                       └──Type expr: Tuple
                                                          └──Type expr: Mu
                                                             └──Variable: a12051
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a12070
                                                                         └──Type expr: Variable: a12051
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: a12056
                                                          └──Type expr: Mu
                                                             └──Variable: a12071
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a12070
                                                                         └──Type expr: Variable: a12071
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: a12076
                                                       └──Type expr: Variable: a12070
                                                 └──Expression:
                                                    └──Type expr: Mu
                                                       └──Variable: a11977
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a12070
                                                                      └──Type expr: Variable: a11977
                                                                └──Type expr: Row uniform
                                                                   └──Type expr: Constructor: absent
                                                    └──Desc: Variable
                                                       └──Variable: t
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Mu
                                                    └──Variable: a12051
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a12070
                                                                └──Type expr: Variable: a12051
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: a12056
                                                 └──Type expr: Mu
                                                    └──Variable: a12071
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a12070
                                                                └──Type expr: Variable: a12071
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: a12076
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Mu
                                                       └──Variable: a12051
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a12070
                                                                   └──Type expr: Variable: a12051
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a12056
                                                    └──Desc: Variant
                                                       └──Variant description:
                                                          └──Tag: Nil
                                                          └──Variant row:
                                                             └──Type expr: Mu
                                                                └──Variable: a12000
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a12070
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Variable: a12000
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: a12056
                                                 └──Expression:
                                                    └──Type expr: Mu
                                                       └──Variable: a12071
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a12070
                                                                   └──Type expr: Variable: a12071
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a12076
                                                    └──Desc: Variant
                                                       └──Variant description:
                                                          └──Tag: Nil
                                                          └──Variant row:
                                                             └──Type expr: Mu
                                                                └──Variable: a12011
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a12070
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Variable: a12011
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: a12076
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: a12070
                                           └──Type expr: Arrow
                                              └──Type expr: Tuple
                                                 └──Type expr: Mu
                                                    └──Variable: a12051
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a12070
                                                                └──Type expr: Variable: a12051
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: a12056
                                                 └──Type expr: Mu
                                                    └──Variable: a12071
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a12070
                                                                └──Type expr: Variable: a12071
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: a12076
                                              └──Type expr: Tuple
                                                 └──Type expr: Mu
                                                    └──Variable: a12051
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a12070
                                                                └──Type expr: Variable: a12051
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: a12056
                                                 └──Type expr: Mu
                                                    └──Variable: a12071
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a12070
                                                                └──Type expr: Variable: a12071
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: a12076
                                        └──Desc: Function
                                           └──Pattern:
                                              └──Type expr: Variable: a12070
                                              └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Tuple
                                                    └──Type expr: Mu
                                                       └──Variable: a12051
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a12070
                                                                   └──Type expr: Variable: a12051
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a12056
                                                    └──Type expr: Mu
                                                       └──Variable: a12071
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a12070
                                                                   └──Type expr: Variable: a12071
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a12076
                                                 └──Type expr: Tuple
                                                    └──Type expr: Mu
                                                       └──Variable: a12051
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a12070
                                                                   └──Type expr: Variable: a12051
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a12056
                                                    └──Type expr: Mu
                                                       └──Variable: a12071
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a12070
                                                                   └──Type expr: Variable: a12071
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a12076
                                              └──Desc: Function
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Mu
                                                          └──Variable: a12051
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a12070
                                                                      └──Type expr: Variable: a12051
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: a12056
                                                       └──Type expr: Mu
                                                          └──Variable: a12071
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a12070
                                                                      └──Type expr: Variable: a12071
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: a12076
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Mu
                                                             └──Variable: a12051
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a12070
                                                                         └──Type expr: Variable: a12051
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: a12056
                                                          └──Desc: Variable: l
                                                       └──Pattern:
                                                          └──Type expr: Mu
                                                             └──Variable: a12071
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a12070
                                                                         └──Type expr: Variable: a12071
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: a12076
                                                          └──Desc: Variable: r
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Mu
                                                          └──Variable: a12051
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a12070
                                                                      └──Type expr: Variable: a12051
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: a12056
                                                       └──Type expr: Mu
                                                          └──Variable: a12071
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a12070
                                                                      └──Type expr: Variable: a12071
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: a12076
                                                    └──Desc: If
                                                       └──Expression:
                                                          └──Type expr: Constructor: bool
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: a12070
                                                                   └──Type expr: Constructor: bool
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Variable: a12070
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Mu
                                                                └──Variable: a12051
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a12070
                                                                            └──Type expr: Variable: a12051
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a12056
                                                             └──Type expr: Mu
                                                                └──Variable: a12071
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a12070
                                                                            └──Type expr: Variable: a12071
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a12076
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Mu
                                                                   └──Variable: a12051
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a12070
                                                                               └──Type expr: Variable: a12051
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: a12056
                                                                └──Desc: Variant
                                                                   └──Variant description:
                                                                      └──Tag: Cons
                                                                      └──Variant row:
                                                                         └──Type expr: Mu
                                                                            └──Variable: a12000
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a12070
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Variable: a12000
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: a12056
                                                                   └──Expression:
                                                                      └──Type expr: Mu
                                                                         └──Variable: a12045
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a12070
                                                                            └──Type expr: Variant
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Cons
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Variable: a12045
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Nil
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Variable: a12056
                                                                      └──Desc: Tuple
                                                                         └──Expression:
                                                                            └──Type expr: Variable: a12070
                                                                            └──Desc: Variable
                                                                               └──Variable: x
                                                                         └──Expression:
                                                                            └──Type expr: Mu
                                                                               └──Variable: a12051
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: a12070
                                                                                           └──Type expr: Variable: a12051
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Nil
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Constructor: unit
                                                                                        └──Type expr: Variable: a12056
                                                                            └──Desc: Variable
                                                                               └──Variable: l
                                                             └──Expression:
                                                                └──Type expr: Mu
                                                                   └──Variable: a12071
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a12070
                                                                               └──Type expr: Variable: a12071
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: a12076
                                                                └──Desc: Variable
                                                                   └──Variable: r
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Mu
                                                                └──Variable: a12051
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a12070
                                                                            └──Type expr: Variable: a12051
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a12056
                                                             └──Type expr: Mu
                                                                └──Variable: a12071
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a12070
                                                                            └──Type expr: Variable: a12071
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a12076
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Mu
                                                                   └──Variable: a12051
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a12070
                                                                               └──Type expr: Variable: a12051
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: a12056
                                                                └──Desc: Variable
                                                                   └──Variable: l
                                                             └──Expression:
                                                                └──Type expr: Mu
                                                                   └──Variable: a12071
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a12070
                                                                               └──Type expr: Variable: a12071
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: a12076
                                                                └──Desc: Variant
                                                                   └──Variant description:
                                                                      └──Tag: Cons
                                                                      └──Variant row:
                                                                         └──Type expr: Mu
                                                                            └──Variable: a12011
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a12070
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Variable: a12011
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: a12076
                                                                   └──Expression:
                                                                      └──Type expr: Mu
                                                                         └──Variable: a12065
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a12070
                                                                            └──Type expr: Variant
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Cons
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Variable: a12065
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Nil
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Variable: a12076
                                                                      └──Desc: Tuple
                                                                         └──Expression:
                                                                            └──Type expr: Variable: a12070
                                                                            └──Desc: Variable
                                                                               └──Variable: x
                                                                         └──Expression:
                                                                            └──Type expr: Mu
                                                                               └──Variable: a12071
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: a12070
                                                                                           └──Type expr: Variable: a12071
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Nil
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Constructor: unit
                                                                                        └──Type expr: Variable: a12076
                                                                            └──Desc: Variable
                                                                               └──Variable: r
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: a12081
                      └──Type expr: Variable: a12081
                   └──Desc: Variable: id
                └──Abstraction:
                   └──Variables: a12081,a12081
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a12081
                         └──Type expr: Variable: a12081
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a12081
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: a12081
                            └──Desc: Variable
                               └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: a12097
                         └──Type expr: Variable: a12094
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: a12100
                            └──Type expr: Variable: a12097
                         └──Type expr: Arrow
                            └──Type expr: Variable: a12100
                            └──Type expr: Variable: a12094
                   └──Desc: Variable: compose
                └──Abstraction:
                   └──Variables: a12094
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: a12097
                            └──Type expr: Variable: a12094
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: a12100
                               └──Type expr: Variable: a12097
                            └──Type expr: Arrow
                               └──Type expr: Variable: a12100
                               └──Type expr: Variable: a12094
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a12097
                               └──Type expr: Variable: a12094
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a12100
                                  └──Type expr: Variable: a12097
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a12100
                                  └──Type expr: Variable: a12094
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a12100
                                     └──Type expr: Variable: a12097
                                  └──Desc: Variable: g
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a12100
                                     └──Type expr: Variable: a12094
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: a12100
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: a12094
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: a12097
                                                 └──Type expr: Variable: a12094
                                              └──Desc: Variable
                                                 └──Variable: f
                                           └──Expression:
                                              └──Type expr: Variable: a12097
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: a12100
                                                       └──Type expr: Variable: a12097
                                                    └──Desc: Variable
                                                       └──Variable: g
                                                 └──Expression:
                                                    └──Type expr: Variable: a12100
                                                    └──Desc: Variable
                                                       └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: a12119
                      └──Type expr: Arrow
                         └──Type expr: Variable: a12120
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Cons
                               └──Type expr: Constructor: present
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: a12119
                                     └──Type expr: Variable: a12120
                               └──Type expr: Variable: a12113
                   └──Desc: Variable: cons
                └──Abstraction:
                   └──Variables: a12119,a12119
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a12119
                         └──Type expr: Arrow
                            └──Type expr: Variable: a12120
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Cons
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: a12119
                                        └──Type expr: Variable: a12120
                                  └──Type expr: Variable: a12113
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a12119
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a12120
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a12119
                                           └──Type expr: Variable: a12120
                                     └──Type expr: Variable: a12113
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: a12120
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a12119
                                              └──Type expr: Variable: a12120
                                        └──Type expr: Variable: a12113
                                  └──Desc: Variant
                                     └──Variant description:
                                        └──Tag: Cons
                                        └──Variant row:
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a12119
                                                    └──Type expr: Variable: a12120
                                              └──Type expr: Variable: a12113
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a12119
                                           └──Type expr: Variable: a12120
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Variable: a12119
                                              └──Desc: Variable
                                                 └──Variable: x
                                           └──Expression:
                                              └──Type expr: Variable: a12120
                                              └──Desc: Variable
                                                 └──Variable: t
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: a12289
                         └──Type expr: Constructor: bool
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: a12289
                            └──Type expr: Arrow
                               └──Type expr: Variable: a12289
                               └──Type expr: Constructor: bool
                         └──Type expr: Arrow
                            └──Type expr: Mu
                               └──Variable: a12309
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a12289
                                           └──Type expr: Variable: a12309
                                     └──Type expr: Row cons
                                        └──Label: Nil
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                            └──Type expr: Arrow
                               └──Type expr: Mu
                                  └──Variable: a12319
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a12289
                                              └──Type expr: Variable: a12319
                                        └──Type expr: Variable: a12321
                               └──Type expr: Mu
                                  └──Variable: a12319
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a12289
                                              └──Type expr: Variable: a12319
                                        └──Type expr: Variable: a12321
                   └──Desc: Variable: sort_append
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: a12289
                            └──Type expr: Constructor: bool
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: a12289
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a12289
                                  └──Type expr: Constructor: bool
                            └──Type expr: Arrow
                               └──Type expr: Mu
                                  └──Variable: a12309
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a12289
                                              └──Type expr: Variable: a12309
                                        └──Type expr: Row cons
                                           └──Label: Nil
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                               └──Type expr: Arrow
                                  └──Type expr: Mu
                                     └──Variable: a12319
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a12289
                                                 └──Type expr: Variable: a12319
                                           └──Type expr: Variable: a12321
                                  └──Type expr: Mu
                                     └──Variable: a12319
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a12289
                                                 └──Type expr: Variable: a12319
                                           └──Type expr: Variable: a12321
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a12289
                               └──Type expr: Constructor: bool
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a12289
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a12289
                                     └──Type expr: Constructor: bool
                               └──Type expr: Arrow
                                  └──Type expr: Mu
                                     └──Variable: a12309
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a12289
                                                 └──Type expr: Variable: a12309
                                           └──Type expr: Row cons
                                              └──Label: Nil
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                                  └──Type expr: Arrow
                                     └──Type expr: Mu
                                        └──Variable: a12319
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a12289
                                                    └──Type expr: Variable: a12319
                                              └──Type expr: Variable: a12321
                                     └──Type expr: Mu
                                        └──Variable: a12319
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a12289
                                                    └──Type expr: Variable: a12319
                                              └──Type expr: Variable: a12321
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a12289
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: a12289
                                        └──Type expr: Constructor: bool
                                  └──Desc: Variable: le
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Mu
                                        └──Variable: a12309
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a12289
                                                    └──Type expr: Variable: a12309
                                              └──Type expr: Row cons
                                                 └──Label: Nil
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                     └──Type expr: Arrow
                                        └──Type expr: Mu
                                           └──Variable: a12319
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Cons
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a12289
                                                       └──Type expr: Variable: a12319
                                                 └──Type expr: Variable: a12321
                                        └──Type expr: Mu
                                           └──Variable: a12319
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Cons
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a12289
                                                       └──Type expr: Variable: a12319
                                                 └──Type expr: Variable: a12321
                                  └──Desc: Let rec
                                     └──Value bindings:
                                        └──Value binding:
                                           └──Variable: loop
                                           └──Abstraction:
                                              └──Variables: a12298
                                              └──Expression:
                                                 └──Type expr: Arrow
                                                    └──Type expr: Mu
                                                       └──Variable: a12301
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a12289
                                                                   └──Type expr: Variable: a12301
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row uniform
                                                                   └──Type expr: Constructor: absent
                                                    └──Type expr: Arrow
                                                       └──Type expr: Mu
                                                          └──Variable: a12283
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a12289
                                                                      └──Type expr: Variable: a12283
                                                                └──Type expr: Variable: a12298
                                                       └──Type expr: Mu
                                                          └──Variable: a12283
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a12289
                                                                      └──Type expr: Variable: a12283
                                                                └──Type expr: Variable: a12298
                                                 └──Desc: Function
                                                    └──Pattern:
                                                       └──Type expr: Mu
                                                          └──Variable: a12301
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a12289
                                                                      └──Type expr: Variable: a12301
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                       └──Desc: Variable: t
                                                    └──Expression:
                                                       └──Type expr: Arrow
                                                          └──Type expr: Mu
                                                             └──Variable: a12283
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a12289
                                                                         └──Type expr: Variable: a12283
                                                                   └──Type expr: Variable: a12298
                                                          └──Type expr: Mu
                                                             └──Variable: a12283
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a12289
                                                                         └──Type expr: Variable: a12283
                                                                   └──Type expr: Variable: a12298
                                                       └──Desc: Match
                                                          └──Expression:
                                                             └──Type expr: Mu
                                                                └──Variable: a12301
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a12289
                                                                            └──Type expr: Variable: a12301
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                                             └──Desc: Variable
                                                                └──Variable: t
                                                          └──Type expr: Mu
                                                             └──Variable: a12301
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a12289
                                                                         └──Type expr: Variable: a12301
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                          └──Cases:
                                                             └──Case:
                                                                └──Pattern:
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Mu
                                                                                  └──Variable: a12221
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a12289
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Variable: a12221
                                                                                           └──Type expr: Row cons
                                                                                              └──Label: Nil
                                                                                              └──Type expr: Constructor: present
                                                                                                 └──Type expr: Constructor: unit
                                                                                              └──Type expr: Row uniform
                                                                                                 └──Type expr: Constructor: absent
                                                                            └──Type expr: Row uniform
                                                                               └──Type expr: Constructor: absent
                                                                   └──Desc: Variant
                                                                      └──Variant description:
                                                                         └──Tag: Nil
                                                                         └──Variant row:
                                                                            └──Type expr: Row cons
                                                                               └──Label: Nil
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Cons
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Mu
                                                                                        └──Variable: a12221
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: a12289
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Variable: a12221
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Nil
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Constructor: unit
                                                                                                    └──Type expr: Row uniform
                                                                                                       └──Type expr: Constructor: absent
                                                                                  └──Type expr: Row uniform
                                                                                     └──Type expr: Constructor: absent
                                                                └──Expression:
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Mu
                                                                         └──Variable: a12283
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a12289
                                                                                     └──Type expr: Variable: a12283
                                                                               └──Type expr: Variable: a12298
                                                                      └──Type expr: Mu
                                                                         └──Variable: a12283
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a12289
                                                                                     └──Type expr: Variable: a12283
                                                                               └──Type expr: Variable: a12298
                                                                   └──Desc: Variable
                                                                      └──Variable: id
                                                                      └──Type expr: Mu
                                                                         └──Variable: a12283
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a12289
                                                                                     └──Type expr: Variable: a12283
                                                                               └──Type expr: Variable: a12298
                                                             └──Case:
                                                                └──Pattern:
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Mu
                                                                                  └──Variable: a12221
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a12289
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Variable: a12221
                                                                                           └──Type expr: Row cons
                                                                                              └──Label: Nil
                                                                                              └──Type expr: Constructor: present
                                                                                                 └──Type expr: Constructor: unit
                                                                                              └──Type expr: Row uniform
                                                                                                 └──Type expr: Constructor: absent
                                                                            └──Type expr: Row uniform
                                                                               └──Type expr: Constructor: absent
                                                                   └──Desc: Variant
                                                                      └──Variant description:
                                                                         └──Tag: Cons
                                                                         └──Variant row:
                                                                            └──Type expr: Row cons
                                                                               └──Label: Nil
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Cons
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Mu
                                                                                        └──Variable: a12221
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: a12289
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Variable: a12221
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Nil
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Constructor: unit
                                                                                                    └──Type expr: Row uniform
                                                                                                       └──Type expr: Constructor: absent
                                                                                  └──Type expr: Row uniform
                                                                                     └──Type expr: Constructor: absent
                                                                      └──Pattern:
                                                                         └──Type expr: Mu
                                                                            └──Variable: a12221
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a12289
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Variable: a12221
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Nil
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Constructor: unit
                                                                                        └──Type expr: Row uniform
                                                                                           └──Type expr: Constructor: absent
                                                                         └──Desc: Tuple
                                                                            └──Pattern:
                                                                               └──Type expr: Variable: a12289
                                                                               └──Desc: Any
                                                                            └──Pattern:
                                                                               └──Type expr: Mu
                                                                                  └──Variable: a12301
                                                                                  └──Type expr: Variant
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Cons
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Variable: a12289
                                                                                              └──Type expr: Variable: a12301
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Nil
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Constructor: unit
                                                                                           └──Type expr: Row uniform
                                                                                              └──Type expr: Constructor: absent
                                                                               └──Desc: Any
                                                                └──Expression:
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Mu
                                                                         └──Variable: a12283
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a12289
                                                                                     └──Type expr: Variable: a12283
                                                                               └──Type expr: Variable: a12298
                                                                      └──Type expr: Mu
                                                                         └──Variable: a12283
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a12289
                                                                                     └──Type expr: Variable: a12283
                                                                               └──Type expr: Variable: a12298
                                                                   └──Desc: Let
                                                                      └──Value bindings:
                                                                         └──Value binding:
                                                                            └──Pattern:
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: a12289
                                                                                  └──Type expr: Mu
                                                                                     └──Variable: a12301
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Variable: a12289
                                                                                                 └──Type expr: Variable: a12301
                                                                                           └──Type expr: Row cons
                                                                                              └──Label: Nil
                                                                                              └──Type expr: Constructor: present
                                                                                                 └──Type expr: Constructor: unit
                                                                                              └──Type expr: Row uniform
                                                                                                 └──Type expr: Constructor: absent
                                                                               └──Desc: Tuple
                                                                                  └──Pattern:
                                                                                     └──Type expr: Variable: a12289
                                                                                     └──Desc: Variable: pivot
                                                                                  └──Pattern:
                                                                                     └──Type expr: Mu
                                                                                        └──Variable: a12301
                                                                                        └──Type expr: Variant
                                                                                           └──Type expr: Row cons
                                                                                              └──Label: Cons
                                                                                              └──Type expr: Constructor: present
                                                                                                 └──Type expr: Tuple
                                                                                                    └──Type expr: Variable: a12289
                                                                                                    └──Type expr: Variable: a12301
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Nil
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Constructor: unit
                                                                                                 └──Type expr: Row uniform
                                                                                                    └──Type expr: Constructor: absent
                                                                                     └──Desc: Variable: t
                                                                            └──Abstraction:
                                                                               └──Variables:
                                                                               └──Expression:
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a12289
                                                                                     └──Type expr: Mu
                                                                                        └──Variable: a12301
                                                                                        └──Type expr: Variant
                                                                                           └──Type expr: Row cons
                                                                                              └──Label: Cons
                                                                                              └──Type expr: Constructor: present
                                                                                                 └──Type expr: Tuple
                                                                                                    └──Type expr: Variable: a12289
                                                                                                    └──Type expr: Variable: a12301
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Nil
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Constructor: unit
                                                                                                 └──Type expr: Row uniform
                                                                                                    └──Type expr: Constructor: absent
                                                                                  └──Desc: Application
                                                                                     └──Expression:
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Variable: a12289
                                                                                              └──Type expr: Constructor: bool
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Variable: a12289
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: a12301
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: a12289
                                                                                                             └──Type expr: Variable: a12301
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Nil
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Constructor: unit
                                                                                                          └──Type expr: Row uniform
                                                                                                             └──Type expr: Constructor: absent
                                                                                        └──Desc: Application
                                                                                           └──Expression:
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: a12301
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a12289
                                                                                                                └──Type expr: Variable: a12301
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Nil
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Constructor: unit
                                                                                                             └──Type expr: Row uniform
                                                                                                                └──Type expr: Constructor: absent
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Variable: a12289
                                                                                                       └──Type expr: Constructor: bool
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: a12289
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: a12301
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: a12289
                                                                                                                      └──Type expr: Variable: a12301
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Nil
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Constructor: unit
                                                                                                                   └──Type expr: Row uniform
                                                                                                                      └──Type expr: Constructor: absent
                                                                                              └──Desc: Variable
                                                                                                 └──Variable: select
                                                                                                 └──Type expr: Variable: a12289
                                                                                           └──Expression:
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: a12301
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: a12289
                                                                                                             └──Type expr: Variable: a12301
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Nil
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Constructor: unit
                                                                                                          └──Type expr: Row uniform
                                                                                                             └──Type expr: Constructor: absent
                                                                                              └──Desc: Variable
                                                                                                 └──Variable: t
                                                                                     └──Expression:
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Variable: a12289
                                                                                           └──Type expr: Constructor: bool
                                                                                        └──Desc: Variable
                                                                                           └──Variable: f
                                                                      └──Expression:
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Mu
                                                                               └──Variable: a12283
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: a12289
                                                                                           └──Type expr: Variable: a12283
                                                                                     └──Type expr: Variable: a12298
                                                                            └──Type expr: Mu
                                                                               └──Variable: a12283
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: a12289
                                                                                           └──Type expr: Variable: a12283
                                                                                     └──Type expr: Variable: a12298
                                                                         └──Desc: Let
                                                                            └──Value bindings:
                                                                               └──Value binding:
                                                                                  └──Pattern:
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Mu
                                                                                           └──Variable: a12301
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: a12289
                                                                                                       └──Type expr: Variable: a12301
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Nil
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Constructor: unit
                                                                                                    └──Type expr: Row uniform
                                                                                                       └──Type expr: Constructor: absent
                                                                                        └──Type expr: Mu
                                                                                           └──Variable: a12301
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: a12289
                                                                                                       └──Type expr: Variable: a12301
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Nil
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Constructor: unit
                                                                                                    └──Type expr: Row uniform
                                                                                                       └──Type expr: Constructor: absent
                                                                                     └──Desc: Tuple
                                                                                        └──Pattern:
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: a12301
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: a12289
                                                                                                          └──Type expr: Variable: a12301
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Nil
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Constructor: unit
                                                                                                       └──Type expr: Row uniform
                                                                                                          └──Type expr: Constructor: absent
                                                                                           └──Desc: Variable: l
                                                                                        └──Pattern:
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: a12301
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: a12289
                                                                                                          └──Type expr: Variable: a12301
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Nil
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Constructor: unit
                                                                                                       └──Type expr: Row uniform
                                                                                                          └──Type expr: Constructor: absent
                                                                                           └──Desc: Variable: r
                                                                                  └──Abstraction:
                                                                                     └──Variables:
                                                                                     └──Expression:
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: a12301
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: a12289
                                                                                                          └──Type expr: Variable: a12301
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Nil
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Constructor: unit
                                                                                                       └──Type expr: Row uniform
                                                                                                          └──Type expr: Constructor: absent
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: a12301
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: a12289
                                                                                                          └──Type expr: Variable: a12301
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Nil
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Constructor: unit
                                                                                                       └──Type expr: Row uniform
                                                                                                          └──Type expr: Constructor: absent
                                                                                        └──Desc: Application
                                                                                           └──Expression:
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Variable: a12289
                                                                                                    └──Type expr: Constructor: bool
                                                                                                 └──Type expr: Tuple
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a12301
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a12289
                                                                                                                   └──Type expr: Variable: a12301
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Nil
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Constructor: unit
                                                                                                                └──Type expr: Row uniform
                                                                                                                   └──Type expr: Constructor: absent
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a12301
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a12289
                                                                                                                   └──Type expr: Variable: a12301
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Nil
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Constructor: unit
                                                                                                                └──Type expr: Row uniform
                                                                                                                   └──Type expr: Constructor: absent
                                                                                              └──Desc: Application
                                                                                                 └──Expression:
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: a12301
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: a12289
                                                                                                                      └──Type expr: Variable: a12301
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Nil
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Constructor: unit
                                                                                                                   └──Type expr: Row uniform
                                                                                                                      └──Type expr: Constructor: absent
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Arrow
                                                                                                             └──Type expr: Variable: a12289
                                                                                                             └──Type expr: Constructor: bool
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Mu
                                                                                                                └──Variable: a12301
                                                                                                                └──Type expr: Variant
                                                                                                                   └──Type expr: Row cons
                                                                                                                      └──Label: Cons
                                                                                                                      └──Type expr: Constructor: present
                                                                                                                         └──Type expr: Tuple
                                                                                                                            └──Type expr: Variable: a12289
                                                                                                                            └──Type expr: Variable: a12301
                                                                                                                      └──Type expr: Row cons
                                                                                                                         └──Label: Nil
                                                                                                                         └──Type expr: Constructor: present
                                                                                                                            └──Type expr: Constructor: unit
                                                                                                                         └──Type expr: Row uniform
                                                                                                                            └──Type expr: Constructor: absent
                                                                                                             └──Type expr: Mu
                                                                                                                └──Variable: a12301
                                                                                                                └──Type expr: Variant
                                                                                                                   └──Type expr: Row cons
                                                                                                                      └──Label: Cons
                                                                                                                      └──Type expr: Constructor: present
                                                                                                                         └──Type expr: Tuple
                                                                                                                            └──Type expr: Variable: a12289
                                                                                                                            └──Type expr: Variable: a12301
                                                                                                                      └──Type expr: Row cons
                                                                                                                         └──Label: Nil
                                                                                                                         └──Type expr: Constructor: present
                                                                                                                            └──Type expr: Constructor: unit
                                                                                                                         └──Type expr: Row uniform
                                                                                                                            └──Type expr: Constructor: absent
                                                                                                    └──Desc: Variable
                                                                                                       └──Variable: partition
                                                                                                 └──Expression:
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a12301
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a12289
                                                                                                                   └──Type expr: Variable: a12301
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Nil
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Constructor: unit
                                                                                                                └──Type expr: Row uniform
                                                                                                                   └──Type expr: Constructor: absent
                                                                                                    └──Desc: Variable
                                                                                                       └──Variable: t
                                                                                           └──Expression:
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Variable: a12289
                                                                                                 └──Type expr: Constructor: bool
                                                                                              └──Desc: Function
                                                                                                 └──Pattern:
                                                                                                    └──Type expr: Variable: a12289
                                                                                                    └──Desc: Variable: y
                                                                                                 └──Expression:
                                                                                                    └──Type expr: Constructor: bool
                                                                                                    └──Desc: Application
                                                                                                       └──Expression:
                                                                                                          └──Type expr: Arrow
                                                                                                             └──Type expr: Variable: a12289
                                                                                                             └──Type expr: Constructor: bool
                                                                                                          └──Desc: Application
                                                                                                             └──Expression:
                                                                                                                └──Type expr: Arrow
                                                                                                                   └──Type expr: Variable: a12289
                                                                                                                   └──Type expr: Arrow
                                                                                                                      └──Type expr: Variable: a12289
                                                                                                                      └──Type expr: Constructor: bool
                                                                                                                └──Desc: Variable
                                                                                                                   └──Variable: le
                                                                                                             └──Expression:
                                                                                                                └──Type expr: Variable: a12289
                                                                                                                └──Desc: Variable
                                                                                                                   └──Variable: y
                                                                                                       └──Expression:
                                                                                                          └──Type expr: Variable: a12289
                                                                                                          └──Desc: Variable
                                                                                                             └──Variable: pivot
                                                                            └──Expression:
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Mu
                                                                                     └──Variable: a12283
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Variable: a12289
                                                                                                 └──Type expr: Variable: a12283
                                                                                           └──Type expr: Variable: a12298
                                                                                  └──Type expr: Mu
                                                                                     └──Variable: a12283
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Variable: a12289
                                                                                                 └──Type expr: Variable: a12283
                                                                                           └──Type expr: Variable: a12298
                                                                               └──Desc: Application
                                                                                  └──Expression:
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: a12283
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: a12289
                                                                                                          └──Type expr: Variable: a12283
                                                                                                    └──Type expr: Variable: a12298
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: a12283
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: a12289
                                                                                                          └──Type expr: Variable: a12283
                                                                                                    └──Type expr: Variable: a12298
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: a12283
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: a12289
                                                                                                          └──Type expr: Variable: a12283
                                                                                                    └──Type expr: Variable: a12298
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: a12283
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: a12289
                                                                                                          └──Type expr: Variable: a12283
                                                                                                    └──Type expr: Variable: a12298
                                                                                     └──Desc: Application
                                                                                        └──Expression:
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: a12283
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a12289
                                                                                                                └──Type expr: Variable: a12283
                                                                                                          └──Type expr: Variable: a12298
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: a12283
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a12289
                                                                                                                └──Type expr: Variable: a12283
                                                                                                          └──Type expr: Variable: a12298
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a12283
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a12289
                                                                                                                   └──Type expr: Variable: a12283
                                                                                                             └──Type expr: Variable: a12298
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a12283
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a12289
                                                                                                                   └──Type expr: Variable: a12283
                                                                                                             └──Type expr: Variable: a12298
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a12283
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a12289
                                                                                                                   └──Type expr: Variable: a12283
                                                                                                             └──Type expr: Variable: a12298
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a12283
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a12289
                                                                                                                   └──Type expr: Variable: a12283
                                                                                                             └──Type expr: Variable: a12298
                                                                                           └──Desc: Variable
                                                                                              └──Variable: compose
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: a12283
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: a12289
                                                                                                             └──Type expr: Variable: a12283
                                                                                                       └──Type expr: Variable: a12298
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: a12283
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: a12289
                                                                                                             └──Type expr: Variable: a12283
                                                                                                       └──Type expr: Variable: a12298
                                                                                        └──Expression:
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: a12283
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: a12289
                                                                                                             └──Type expr: Variable: a12283
                                                                                                       └──Type expr: Variable: a12298
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: a12283
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: a12289
                                                                                                             └──Type expr: Variable: a12283
                                                                                                       └──Type expr: Variable: a12298
                                                                                           └──Desc: Application
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a12301
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a12289
                                                                                                                   └──Type expr: Variable: a12301
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Nil
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Constructor: unit
                                                                                                                └──Type expr: Row uniform
                                                                                                                   └──Type expr: Constructor: absent
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: a12283
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: a12289
                                                                                                                      └──Type expr: Variable: a12283
                                                                                                                └──Type expr: Variable: a12298
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: a12283
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: a12289
                                                                                                                      └──Type expr: Variable: a12283
                                                                                                                └──Type expr: Variable: a12298
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: loop
                                                                                              └──Expression:
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: a12301
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a12289
                                                                                                                └──Type expr: Variable: a12301
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Nil
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Constructor: unit
                                                                                                             └──Type expr: Row uniform
                                                                                                                └──Type expr: Constructor: absent
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: l
                                                                                  └──Expression:
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Mu
                                                                                           └──Variable: a12283
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: a12289
                                                                                                       └──Type expr: Variable: a12283
                                                                                                 └──Type expr: Variable: a12298
                                                                                        └──Type expr: Mu
                                                                                           └──Variable: a12283
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: a12289
                                                                                                       └──Type expr: Variable: a12283
                                                                                                 └──Type expr: Variable: a12298
                                                                                     └──Desc: Application
                                                                                        └──Expression:
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: a12283
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a12289
                                                                                                                └──Type expr: Variable: a12283
                                                                                                          └──Type expr: Variable: a12298
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: a12283
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a12289
                                                                                                                └──Type expr: Variable: a12283
                                                                                                          └──Type expr: Variable: a12298
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: a12283
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a12289
                                                                                                                └──Type expr: Variable: a12283
                                                                                                          └──Type expr: Variable: a12298
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: a12283
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a12289
                                                                                                                └──Type expr: Variable: a12283
                                                                                                          └──Type expr: Variable: a12298
                                                                                           └──Desc: Application
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: a12283
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: a12289
                                                                                                                      └──Type expr: Variable: a12283
                                                                                                                └──Type expr: Variable: a12298
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: a12283
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: a12289
                                                                                                                      └──Type expr: Variable: a12283
                                                                                                                └──Type expr: Variable: a12298
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Mu
                                                                                                             └──Variable: a12283
                                                                                                             └──Type expr: Variant
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Cons
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Tuple
                                                                                                                         └──Type expr: Variable: a12289
                                                                                                                         └──Type expr: Variable: a12283
                                                                                                                   └──Type expr: Variable: a12298
                                                                                                          └──Type expr: Mu
                                                                                                             └──Variable: a12283
                                                                                                             └──Type expr: Variant
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Cons
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Tuple
                                                                                                                         └──Type expr: Variable: a12289
                                                                                                                         └──Type expr: Variable: a12283
                                                                                                                   └──Type expr: Variable: a12298
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Mu
                                                                                                             └──Variable: a12283
                                                                                                             └──Type expr: Variant
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Cons
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Tuple
                                                                                                                         └──Type expr: Variable: a12289
                                                                                                                         └──Type expr: Variable: a12283
                                                                                                                   └──Type expr: Variable: a12298
                                                                                                          └──Type expr: Mu
                                                                                                             └──Variable: a12283
                                                                                                             └──Type expr: Variant
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Cons
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Tuple
                                                                                                                         └──Type expr: Variable: a12289
                                                                                                                         └──Type expr: Variable: a12283
                                                                                                                   └──Type expr: Variable: a12298
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: compose
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a12283
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a12289
                                                                                                                   └──Type expr: Variable: a12283
                                                                                                             └──Type expr: Variable: a12298
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a12283
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a12289
                                                                                                                   └──Type expr: Variable: a12283
                                                                                                             └──Type expr: Variable: a12298
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a12283
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a12289
                                                                                                                   └──Type expr: Variable: a12283
                                                                                                             └──Type expr: Variable: a12298
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a12283
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a12289
                                                                                                                   └──Type expr: Variable: a12283
                                                                                                             └──Type expr: Variable: a12298
                                                                                                 └──Desc: Application
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Variable: a12289
                                                                                                          └──Type expr: Arrow
                                                                                                             └──Type expr: Mu
                                                                                                                └──Variable: a12283
                                                                                                                └──Type expr: Variant
                                                                                                                   └──Type expr: Row cons
                                                                                                                      └──Label: Cons
                                                                                                                      └──Type expr: Constructor: present
                                                                                                                         └──Type expr: Tuple
                                                                                                                            └──Type expr: Variable: a12289
                                                                                                                            └──Type expr: Variable: a12283
                                                                                                                      └──Type expr: Variable: a12298
                                                                                                             └──Type expr: Mu
                                                                                                                └──Variable: a12283
                                                                                                                └──Type expr: Variant
                                                                                                                   └──Type expr: Row cons
                                                                                                                      └──Label: Cons
                                                                                                                      └──Type expr: Constructor: present
                                                                                                                         └──Type expr: Tuple
                                                                                                                            └──Type expr: Variable: a12289
                                                                                                                            └──Type expr: Variable: a12283
                                                                                                                      └──Type expr: Variable: a12298
                                                                                                       └──Desc: Variable
                                                                                                          └──Variable: cons
                                                                                                          └──Type expr: Mu
                                                                                                             └──Variable: a12283
                                                                                                             └──Type expr: Variant
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Cons
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Tuple
                                                                                                                         └──Type expr: Variable: a12289
                                                                                                                         └──Type expr: Variable: a12283
                                                                                                                   └──Type expr: Variable: a12298
                                                                                                          └──Type expr: Variable: a12289
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Variable: a12289
                                                                                                       └──Desc: Variable
                                                                                                          └──Variable: pivot
                                                                                        └──Expression:
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: a12283
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: a12289
                                                                                                             └──Type expr: Variable: a12283
                                                                                                       └──Type expr: Variable: a12298
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: a12283
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: a12289
                                                                                                             └──Type expr: Variable: a12283
                                                                                                       └──Type expr: Variable: a12298
                                                                                           └──Desc: Application
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a12301
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a12289
                                                                                                                   └──Type expr: Variable: a12301
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Nil
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Constructor: unit
                                                                                                                └──Type expr: Row uniform
                                                                                                                   └──Type expr: Constructor: absent
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: a12283
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: a12289
                                                                                                                      └──Type expr: Variable: a12283
                                                                                                                └──Type expr: Variable: a12298
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: a12283
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: a12289
                                                                                                                      └──Type expr: Variable: a12283
                                                                                                                └──Type expr: Variable: a12298
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: loop
                                                                                              └──Expression:
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: a12301
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a12289
                                                                                                                └──Type expr: Variable: a12301
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Nil
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Constructor: unit
                                                                                                             └──Type expr: Row uniform
                                                                                                                └──Type expr: Constructor: absent
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: r
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Mu
                                              └──Variable: a12309
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Cons
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a12289
                                                          └──Type expr: Variable: a12309
                                                    └──Type expr: Row cons
                                                       └──Label: Nil
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row uniform
                                                          └──Type expr: Constructor: absent
                                           └──Type expr: Arrow
                                              └──Type expr: Mu
                                                 └──Variable: a12319
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a12289
                                                             └──Type expr: Variable: a12319
                                                       └──Type expr: Variable: a12321
                                              └──Type expr: Mu
                                                 └──Variable: a12319
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a12289
                                                             └──Type expr: Variable: a12319
                                                       └──Type expr: Variable: a12321
                                        └──Desc: Variable
                                           └──Variable: loop
                                           └──Type expr: Variable: a12321
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Mu
                         └──Variable: a12336
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Cons
                               └──Type expr: Constructor: present
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: a12347
                                     └──Type expr: Variable: a12336
                               └──Type expr: Row cons
                                  └──Label: Nil
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: a12347
                            └──Type expr: Arrow
                               └──Type expr: Variable: a12347
                               └──Type expr: Constructor: bool
                         └──Type expr: Mu
                            └──Variable: a12330
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Cons
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: a12347
                                        └──Type expr: Variable: a12330
                                  └──Type expr: Row cons
                                     └──Label: Nil
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Variable: a12386
                   └──Desc: Variable: sort
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Mu
                            └──Variable: a12336
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Cons
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: a12347
                                        └──Type expr: Variable: a12336
                                  └──Type expr: Row cons
                                     └──Label: Nil
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: a12347
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a12347
                                  └──Type expr: Constructor: bool
                            └──Type expr: Mu
                               └──Variable: a12330
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a12347
                                           └──Type expr: Variable: a12330
                                     └──Type expr: Row cons
                                        └──Label: Nil
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Variable: a12386
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Mu
                               └──Variable: a12336
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a12347
                                           └──Type expr: Variable: a12336
                                     └──Type expr: Row cons
                                        └──Label: Nil
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a12347
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a12347
                                     └──Type expr: Constructor: bool
                               └──Type expr: Mu
                                  └──Variable: a12330
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a12347
                                              └──Type expr: Variable: a12330
                                        └──Type expr: Row cons
                                           └──Label: Nil
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: a12386
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a12347
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: a12347
                                        └──Type expr: Constructor: bool
                                  └──Desc: Variable: le
                               └──Expression:
                                  └──Type expr: Mu
                                     └──Variable: a12330
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a12347
                                                 └──Type expr: Variable: a12330
                                           └──Type expr: Row cons
                                              └──Label: Nil
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Variable: a12386
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Mu
                                              └──Variable: a12330
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Cons
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a12347
                                                          └──Type expr: Variable: a12330
                                                    └──Type expr: Row cons
                                                       └──Label: Nil
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Variable: a12386
                                           └──Type expr: Mu
                                              └──Variable: a12330
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Cons
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a12347
                                                          └──Type expr: Variable: a12330
                                                    └──Type expr: Row cons
                                                       └──Label: Nil
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Variable: a12386
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Mu
                                                    └──Variable: a12336
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a12347
                                                                └──Type expr: Variable: a12336
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                                 └──Type expr: Arrow
                                                    └──Type expr: Mu
                                                       └──Variable: a12330
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a12347
                                                                   └──Type expr: Variable: a12330
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a12386
                                                    └──Type expr: Mu
                                                       └──Variable: a12330
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a12347
                                                                   └──Type expr: Variable: a12330
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a12386
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: a12347
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a12347
                                                             └──Type expr: Constructor: bool
                                                       └──Type expr: Arrow
                                                          └──Type expr: Mu
                                                             └──Variable: a12336
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a12347
                                                                         └──Type expr: Variable: a12336
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                          └──Type expr: Arrow
                                                             └──Type expr: Mu
                                                                └──Variable: a12330
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a12347
                                                                            └──Type expr: Variable: a12330
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a12386
                                                             └──Type expr: Mu
                                                                └──Variable: a12330
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a12347
                                                                            └──Type expr: Variable: a12330
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a12386
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a12347
                                                                └──Type expr: Constructor: bool
                                                             └──Type expr: Arrow
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: a12347
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: a12347
                                                                      └──Type expr: Constructor: bool
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Mu
                                                                      └──Variable: a12336
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: a12347
                                                                                  └──Type expr: Variable: a12336
                                                                            └──Type expr: Row cons
                                                                               └──Label: Nil
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row uniform
                                                                                  └──Type expr: Constructor: absent
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Mu
                                                                         └──Variable: a12330
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a12347
                                                                                     └──Type expr: Variable: a12330
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: a12386
                                                                      └──Type expr: Mu
                                                                         └──Variable: a12330
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a12347
                                                                                     └──Type expr: Variable: a12330
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: a12386
                                                          └──Desc: Variable
                                                             └──Variable: sort_append
                                                             └──Type expr: Variable: a12347
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a12347
                                                             └──Type expr: Constructor: bool
                                                          └──Desc: Function
                                                             └──Pattern:
                                                                └──Type expr: Variable: a12347
                                                                └──Desc: Variable: x
                                                             └──Expression:
                                                                └──Type expr: Constructor: bool
                                                                └──Desc: Constant: true
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: a12347
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: a12347
                                                          └──Type expr: Constructor: bool
                                                    └──Desc: Variable
                                                       └──Variable: le
                                           └──Expression:
                                              └──Type expr: Mu
                                                 └──Variable: a12336
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a12347
                                                             └──Type expr: Variable: a12336
                                                       └──Type expr: Row cons
                                                          └──Label: Nil
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                              └──Desc: Variable
                                                 └──Variable: t
                                     └──Expression:
                                        └──Type expr: Mu
                                           └──Variable: a12330
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Cons
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a12347
                                                       └──Type expr: Variable: a12330
                                                 └──Type expr: Row cons
                                                    └──Label: Nil
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Variable: a12386
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Nil
                                              └──Variant row:
                                                 └──Type expr: Mu
                                                    └──Variable: a12365
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a12347
                                                             └──Type expr: Variant
                                                                └──Type expr: Variable: a12365
                                                       └──Type expr: Row cons
                                                          └──Label: Nil
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Variable: a12386 |}]