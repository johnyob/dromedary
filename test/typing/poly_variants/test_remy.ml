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
                └──Variables: a6298
                └──Type expr: Arrow
                   └──Type expr: Constructor: string
                   └──Type expr: Variable: a6298
             └──Primitive name: %failwith
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: select
                └──Abstraction:
                   └──Variables: a6384
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Mu
                            └──Variable: a6385
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Cons
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: a6384
                                        └──Type expr: Variable: a6385
                                  └──Type expr: Row cons
                                     └──Label: Nil
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: a6384
                               └──Type expr: Constructor: bool
                            └──Type expr: Tuple
                               └──Type expr: Variable: a6384
                               └──Type expr: Mu
                                  └──Variable: a6385
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a6384
                                              └──Type expr: Variable: a6385
                                        └──Type expr: Row cons
                                           └──Label: Nil
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Mu
                               └──Variable: a6385
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a6384
                                           └──Type expr: Variable: a6385
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
                                  └──Type expr: Variable: a6384
                                  └──Type expr: Constructor: bool
                               └──Type expr: Tuple
                                  └──Type expr: Variable: a6384
                                  └──Type expr: Mu
                                     └──Variable: a6385
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a6384
                                                 └──Type expr: Variable: a6385
                                           └──Type expr: Row cons
                                              └──Label: Nil
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a6384
                                     └──Type expr: Constructor: bool
                                  └──Desc: Variable: f
                               └──Expression:
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: a6384
                                     └──Type expr: Mu
                                        └──Variable: a6385
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a6384
                                                    └──Type expr: Variable: a6385
                                              └──Type expr: Row cons
                                                 └──Label: Nil
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Mu
                                           └──Variable: a6385
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Cons
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a6384
                                                       └──Type expr: Variable: a6385
                                                 └──Type expr: Row cons
                                                    └──Label: Nil
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                        └──Desc: Variable
                                           └──Variable: t1
                                     └──Type expr: Mu
                                        └──Variable: a6385
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a6384
                                                    └──Type expr: Variable: a6385
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
                                                             └──Variable: a6317
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a6384
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Variable: a6317
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
                                                                   └──Variable: a6317
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a6384
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Variable: a6317
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
                                                 └──Type expr: Variable: a6384
                                                 └──Type expr: Mu
                                                    └──Variable: a6385
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a6384
                                                                └──Type expr: Variable: a6385
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
                                                          └──Type expr: Variable: a6384
                                                          └──Type expr: Mu
                                                             └──Variable: a6385
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a6384
                                                                         └──Type expr: Variable: a6385
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                    └──Desc: Variable
                                                       └──Variable: failwith
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a6384
                                                          └──Type expr: Mu
                                                             └──Variable: a6385
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a6384
                                                                         └──Type expr: Variable: a6385
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
                                                             └──Variable: a6317
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a6384
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Variable: a6317
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
                                                                   └──Variable: a6317
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a6384
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Variable: a6317
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
                                                       └──Variable: a6317
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a6384
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Variable: a6317
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Variable: a6384
                                                          └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Mu
                                                             └──Variable: a6385
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a6384
                                                                         └──Type expr: Variable: a6385
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                          └──Desc: Variable: t2
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a6384
                                                 └──Type expr: Mu
                                                    └──Variable: a6385
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a6384
                                                                └──Type expr: Variable: a6385
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
                                                             └──Type expr: Variable: a6384
                                                             └──Type expr: Constructor: bool
                                                          └──Desc: Variable
                                                             └──Variable: f
                                                       └──Expression:
                                                          └──Type expr: Variable: a6384
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a6384
                                                       └──Type expr: Mu
                                                          └──Variable: a6385
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a6384
                                                                      └──Type expr: Variable: a6385
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Variable: a6384
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Mu
                                                             └──Variable: a6385
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a6384
                                                                         └──Type expr: Variable: a6385
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
                                                       └──Type expr: Variable: a6384
                                                       └──Type expr: Mu
                                                          └──Variable: a6385
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a6384
                                                                      └──Type expr: Variable: a6385
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
                                                                   └──Type expr: Variable: a6384
                                                                   └──Type expr: Mu
                                                                      └──Variable: a6385
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: a6384
                                                                                  └──Type expr: Variable: a6385
                                                                            └──Type expr: Row cons
                                                                               └──Label: Nil
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row uniform
                                                                                  └──Type expr: Constructor: absent
                                                                └──Desc: Tuple
                                                                   └──Pattern:
                                                                      └──Type expr: Variable: a6384
                                                                      └──Desc: Variable: y
                                                                   └──Pattern:
                                                                      └──Type expr: Mu
                                                                         └──Variable: a6385
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a6384
                                                                                     └──Type expr: Variable: a6385
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
                                                                      └──Type expr: Variable: a6384
                                                                      └──Type expr: Mu
                                                                         └──Variable: a6385
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a6384
                                                                                     └──Type expr: Variable: a6385
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
                                                                               └──Type expr: Variable: a6384
                                                                               └──Type expr: Constructor: bool
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a6384
                                                                               └──Type expr: Mu
                                                                                  └──Variable: a6385
                                                                                  └──Type expr: Variant
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Cons
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Variable: a6384
                                                                                              └──Type expr: Variable: a6385
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
                                                                                     └──Variable: a6385
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Variable: a6384
                                                                                                 └──Type expr: Variable: a6385
                                                                                           └──Type expr: Row cons
                                                                                              └──Label: Nil
                                                                                              └──Type expr: Constructor: present
                                                                                                 └──Type expr: Constructor: unit
                                                                                              └──Type expr: Row uniform
                                                                                                 └──Type expr: Constructor: absent
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Variable: a6384
                                                                                        └──Type expr: Constructor: bool
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Variable: a6384
                                                                                        └──Type expr: Mu
                                                                                           └──Variable: a6385
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: a6384
                                                                                                       └──Type expr: Variable: a6385
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
                                                                                  └──Variable: a6385
                                                                                  └──Type expr: Variant
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Cons
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Variable: a6384
                                                                                              └──Type expr: Variable: a6385
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
                                                                            └──Type expr: Variable: a6384
                                                                            └──Type expr: Constructor: bool
                                                                         └──Desc: Variable
                                                                            └──Variable: f
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a6384
                                                             └──Type expr: Mu
                                                                └──Variable: a6385
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a6384
                                                                            └──Type expr: Variable: a6385
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Variable: a6384
                                                                └──Desc: Variable
                                                                   └──Variable: y
                                                             └──Expression:
                                                                └──Type expr: Mu
                                                                   └──Variable: a6385
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a6384
                                                                               └──Type expr: Variable: a6385
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
                                                                            └──Variable: a6324
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a6384
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Variable: a6324
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row uniform
                                                                                     └──Type expr: Constructor: absent
                                                                   └──Expression:
                                                                      └──Type expr: Mu
                                                                         └──Variable: a6317
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a6384
                                                                            └──Type expr: Variant
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Cons
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Variable: a6317
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Nil
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Row uniform
                                                                                        └──Type expr: Constructor: absent
                                                                      └──Desc: Tuple
                                                                         └──Expression:
                                                                            └──Type expr: Variable: a6384
                                                                            └──Desc: Variable
                                                                               └──Variable: x
                                                                         └──Expression:
                                                                            └──Type expr: Mu
                                                                               └──Variable: a6385
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: a6384
                                                                                           └──Type expr: Variable: a6385
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
                   └──Variables: a6443,a6446
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Mu
                            └──Variable: a6455
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Nil
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a6446
                                           └──Type expr: Variable: a6455
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                         └──Type expr: Arrow
                            └──Type expr: Variable: a6443
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a6446
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a6443
                                     └──Type expr: Variable: a6443
                               └──Type expr: Variable: a6443
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Mu
                               └──Variable: a6455
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Nil
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a6446
                                              └──Type expr: Variable: a6455
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a6443
                               └──Type expr: Arrow
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a6446
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: a6443
                                        └──Type expr: Variable: a6443
                                  └──Type expr: Variable: a6443
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: a6443
                                  └──Desc: Variable: init
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: a6446
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: a6443
                                           └──Type expr: Variable: a6443
                                     └──Type expr: Variable: a6443
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: a6446
                                           └──Type expr: Arrow
                                              └──Type expr: Variable: a6443
                                              └──Type expr: Variable: a6443
                                        └──Desc: Variable: f
                                     └──Expression:
                                        └──Type expr: Variable: a6443
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Mu
                                                 └──Variable: a6455
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Nil
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a6446
                                                                └──Type expr: Variable: a6455
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                              └──Desc: Variable
                                                 └──Variable: t
                                           └──Type expr: Mu
                                              └──Variable: a6455
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Nil
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a6446
                                                             └──Type expr: Variable: a6455
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
                                                                   └──Variable: a6415
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a6446
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Variable: a6415
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
                                                                         └──Variable: a6415
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a6446
                                                                            └──Type expr: Variant
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Variable: a6415
                                                                                     └──Type expr: Row uniform
                                                                                        └──Type expr: Constructor: absent
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                 └──Expression:
                                                    └──Type expr: Variable: a6443
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
                                                                   └──Variable: a6415
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a6446
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Variable: a6415
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
                                                                         └──Variable: a6415
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a6446
                                                                            └──Type expr: Variant
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Variable: a6415
                                                                                     └──Type expr: Row uniform
                                                                                        └──Type expr: Constructor: absent
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                       └──Pattern:
                                                          └──Type expr: Mu
                                                             └──Variable: a6415
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a6446
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Variable: a6415
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Variable: a6446
                                                                └──Desc: Variable: x
                                                             └──Pattern:
                                                                └──Type expr: Mu
                                                                   └──Variable: a6455
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: a6446
                                                                                  └──Type expr: Variable: a6455
                                                                            └──Type expr: Row uniform
                                                                               └──Type expr: Constructor: absent
                                                                └──Desc: Variable: t
                                                 └──Expression:
                                                    └──Type expr: Variable: a6443
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a6443
                                                             └──Type expr: Variable: a6443
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: a6446
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: a6443
                                                                      └──Type expr: Variable: a6443
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Variable: a6446
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Variable: a6443
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: a6446
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: a6443
                                                                         └──Type expr: Variable: a6443
                                                                   └──Type expr: Variable: a6443
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: a6443
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Variable: a6446
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Variable: a6443
                                                                                  └──Type expr: Variable: a6443
                                                                            └──Type expr: Variable: a6443
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Mu
                                                                                  └──Variable: a6455
                                                                                  └──Type expr: Variant
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Nil
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Constructor: unit
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Variable: a6446
                                                                                                 └──Type expr: Variable: a6455
                                                                                           └──Type expr: Row uniform
                                                                                              └──Type expr: Constructor: absent
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Variable: a6443
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Variable: a6446
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Variable: a6443
                                                                                           └──Type expr: Variable: a6443
                                                                                     └──Type expr: Variable: a6443
                                                                            └──Desc: Variable
                                                                               └──Variable: fold_right
                                                                         └──Expression:
                                                                            └──Type expr: Mu
                                                                               └──Variable: a6455
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Nil
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Cons
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Variable: a6446
                                                                                              └──Type expr: Variable: a6455
                                                                                        └──Type expr: Row uniform
                                                                                           └──Type expr: Constructor: absent
                                                                            └──Desc: Variable
                                                                               └──Variable: t
                                                                   └──Expression:
                                                                      └──Type expr: Variable: a6443
                                                                      └──Desc: Variable
                                                                         └──Variable: init
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: a6446
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: a6443
                                                                      └──Type expr: Variable: a6443
                                                                └──Desc: Variable
                                                                   └──Variable: f
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Mu
                         └──Variable: a6477
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Nil
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Row cons
                                  └──Label: Cons
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: a6570
                                        └──Type expr: Variable: a6477
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: a6570
                            └──Type expr: Constructor: bool
                         └──Type expr: Tuple
                            └──Type expr: Mu
                               └──Variable: a6551
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a6570
                                           └──Type expr: Variable: a6551
                                     └──Type expr: Row cons
                                        └──Label: Nil
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Variable: a6556
                            └──Type expr: Mu
                               └──Variable: a6571
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a6570
                                           └──Type expr: Variable: a6571
                                     └──Type expr: Row cons
                                        └──Label: Nil
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Variable: a6576
                   └──Desc: Variable: partition
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Mu
                            └──Variable: a6477
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Nil
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a6570
                                           └──Type expr: Variable: a6477
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: a6570
                               └──Type expr: Constructor: bool
                            └──Type expr: Tuple
                               └──Type expr: Mu
                                  └──Variable: a6551
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a6570
                                              └──Type expr: Variable: a6551
                                        └──Type expr: Row cons
                                           └──Label: Nil
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: a6556
                               └──Type expr: Mu
                                  └──Variable: a6571
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a6570
                                              └──Type expr: Variable: a6571
                                        └──Type expr: Row cons
                                           └──Label: Nil
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: a6576
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Mu
                               └──Variable: a6477
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Nil
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a6570
                                              └──Type expr: Variable: a6477
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a6570
                                  └──Type expr: Constructor: bool
                               └──Type expr: Tuple
                                  └──Type expr: Mu
                                     └──Variable: a6551
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a6570
                                                 └──Type expr: Variable: a6551
                                           └──Type expr: Row cons
                                              └──Label: Nil
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Variable: a6556
                                  └──Type expr: Mu
                                     └──Variable: a6571
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a6570
                                                 └──Type expr: Variable: a6571
                                           └──Type expr: Row cons
                                              └──Label: Nil
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Variable: a6576
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a6570
                                     └──Type expr: Constructor: bool
                                  └──Desc: Variable: f
                               └──Expression:
                                  └──Type expr: Tuple
                                     └──Type expr: Mu
                                        └──Variable: a6551
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a6570
                                                    └──Type expr: Variable: a6551
                                              └──Type expr: Row cons
                                                 └──Label: Nil
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Variable: a6556
                                     └──Type expr: Mu
                                        └──Variable: a6571
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a6570
                                                    └──Type expr: Variable: a6571
                                              └──Type expr: Row cons
                                                 └──Label: Nil
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Variable: a6576
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Variable: a6570
                                              └──Type expr: Arrow
                                                 └──Type expr: Tuple
                                                    └──Type expr: Mu
                                                       └──Variable: a6551
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a6570
                                                                   └──Type expr: Variable: a6551
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a6556
                                                    └──Type expr: Mu
                                                       └──Variable: a6571
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a6570
                                                                   └──Type expr: Variable: a6571
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a6576
                                                 └──Type expr: Tuple
                                                    └──Type expr: Mu
                                                       └──Variable: a6551
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a6570
                                                                   └──Type expr: Variable: a6551
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a6556
                                                    └──Type expr: Mu
                                                       └──Variable: a6571
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a6570
                                                                   └──Type expr: Variable: a6571
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a6576
                                           └──Type expr: Tuple
                                              └──Type expr: Mu
                                                 └──Variable: a6551
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a6570
                                                             └──Type expr: Variable: a6551
                                                       └──Type expr: Row cons
                                                          └──Label: Nil
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Variable: a6556
                                              └──Type expr: Mu
                                                 └──Variable: a6571
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a6570
                                                             └──Type expr: Variable: a6571
                                                       └──Type expr: Row cons
                                                          └──Label: Nil
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Variable: a6576
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Tuple
                                                    └──Type expr: Mu
                                                       └──Variable: a6551
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a6570
                                                                   └──Type expr: Variable: a6551
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a6556
                                                    └──Type expr: Mu
                                                       └──Variable: a6571
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a6570
                                                                   └──Type expr: Variable: a6571
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a6576
                                                 └──Type expr: Arrow
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: a6570
                                                       └──Type expr: Arrow
                                                          └──Type expr: Tuple
                                                             └──Type expr: Mu
                                                                └──Variable: a6551
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a6570
                                                                            └──Type expr: Variable: a6551
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a6556
                                                             └──Type expr: Mu
                                                                └──Variable: a6571
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a6570
                                                                            └──Type expr: Variable: a6571
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a6576
                                                          └──Type expr: Tuple
                                                             └──Type expr: Mu
                                                                └──Variable: a6551
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a6570
                                                                            └──Type expr: Variable: a6551
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a6556
                                                             └──Type expr: Mu
                                                                └──Variable: a6571
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a6570
                                                                            └──Type expr: Variable: a6571
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a6576
                                                    └──Type expr: Tuple
                                                       └──Type expr: Mu
                                                          └──Variable: a6551
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a6570
                                                                      └──Type expr: Variable: a6551
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: a6556
                                                       └──Type expr: Mu
                                                          └──Variable: a6571
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a6570
                                                                      └──Type expr: Variable: a6571
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: a6576
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Mu
                                                          └──Variable: a6477
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a6570
                                                                         └──Type expr: Variable: a6477
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                       └──Type expr: Arrow
                                                          └──Type expr: Tuple
                                                             └──Type expr: Mu
                                                                └──Variable: a6551
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a6570
                                                                            └──Type expr: Variable: a6551
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a6556
                                                             └──Type expr: Mu
                                                                └──Variable: a6571
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a6570
                                                                            └──Type expr: Variable: a6571
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a6576
                                                          └──Type expr: Arrow
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a6570
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Mu
                                                                         └──Variable: a6551
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a6570
                                                                                     └──Type expr: Variable: a6551
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: a6556
                                                                      └──Type expr: Mu
                                                                         └──Variable: a6571
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a6570
                                                                                     └──Type expr: Variable: a6571
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: a6576
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Mu
                                                                         └──Variable: a6551
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a6570
                                                                                     └──Type expr: Variable: a6551
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: a6556
                                                                      └──Type expr: Mu
                                                                         └──Variable: a6571
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a6570
                                                                                     └──Type expr: Variable: a6571
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: a6576
                                                             └──Type expr: Tuple
                                                                └──Type expr: Mu
                                                                   └──Variable: a6551
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a6570
                                                                               └──Type expr: Variable: a6551
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: a6556
                                                                └──Type expr: Mu
                                                                   └──Variable: a6571
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a6570
                                                                               └──Type expr: Variable: a6571
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: a6576
                                                    └──Desc: Variable
                                                       └──Variable: fold_right
                                                       └──Type expr: Tuple
                                                          └──Type expr: Mu
                                                             └──Variable: a6551
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a6570
                                                                         └──Type expr: Variable: a6551
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: a6556
                                                          └──Type expr: Mu
                                                             └──Variable: a6571
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a6570
                                                                         └──Type expr: Variable: a6571
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: a6576
                                                       └──Type expr: Variable: a6570
                                                 └──Expression:
                                                    └──Type expr: Mu
                                                       └──Variable: a6477
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a6570
                                                                      └──Type expr: Variable: a6477
                                                                └──Type expr: Row uniform
                                                                   └──Type expr: Constructor: absent
                                                    └──Desc: Variable
                                                       └──Variable: t
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Mu
                                                    └──Variable: a6551
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a6570
                                                                └──Type expr: Variable: a6551
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: a6556
                                                 └──Type expr: Mu
                                                    └──Variable: a6571
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a6570
                                                                └──Type expr: Variable: a6571
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: a6576
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Mu
                                                       └──Variable: a6551
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a6570
                                                                   └──Type expr: Variable: a6551
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a6556
                                                    └──Desc: Variant
                                                       └──Variant description:
                                                          └──Tag: Nil
                                                          └──Variant row:
                                                             └──Type expr: Mu
                                                                └──Variable: a6500
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a6570
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Variable: a6500
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: a6556
                                                 └──Expression:
                                                    └──Type expr: Mu
                                                       └──Variable: a6571
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a6570
                                                                   └──Type expr: Variable: a6571
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a6576
                                                    └──Desc: Variant
                                                       └──Variant description:
                                                          └──Tag: Nil
                                                          └──Variant row:
                                                             └──Type expr: Mu
                                                                └──Variable: a6511
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a6570
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Variable: a6511
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: a6576
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: a6570
                                           └──Type expr: Arrow
                                              └──Type expr: Tuple
                                                 └──Type expr: Mu
                                                    └──Variable: a6551
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a6570
                                                                └──Type expr: Variable: a6551
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: a6556
                                                 └──Type expr: Mu
                                                    └──Variable: a6571
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a6570
                                                                └──Type expr: Variable: a6571
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: a6576
                                              └──Type expr: Tuple
                                                 └──Type expr: Mu
                                                    └──Variable: a6551
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a6570
                                                                └──Type expr: Variable: a6551
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: a6556
                                                 └──Type expr: Mu
                                                    └──Variable: a6571
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a6570
                                                                └──Type expr: Variable: a6571
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: a6576
                                        └──Desc: Function
                                           └──Pattern:
                                              └──Type expr: Variable: a6570
                                              └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Tuple
                                                    └──Type expr: Mu
                                                       └──Variable: a6551
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a6570
                                                                   └──Type expr: Variable: a6551
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a6556
                                                    └──Type expr: Mu
                                                       └──Variable: a6571
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a6570
                                                                   └──Type expr: Variable: a6571
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a6576
                                                 └──Type expr: Tuple
                                                    └──Type expr: Mu
                                                       └──Variable: a6551
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a6570
                                                                   └──Type expr: Variable: a6551
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a6556
                                                    └──Type expr: Mu
                                                       └──Variable: a6571
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a6570
                                                                   └──Type expr: Variable: a6571
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a6576
                                              └──Desc: Function
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Mu
                                                          └──Variable: a6551
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a6570
                                                                      └──Type expr: Variable: a6551
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: a6556
                                                       └──Type expr: Mu
                                                          └──Variable: a6571
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a6570
                                                                      └──Type expr: Variable: a6571
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: a6576
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Mu
                                                             └──Variable: a6551
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a6570
                                                                         └──Type expr: Variable: a6551
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: a6556
                                                          └──Desc: Variable: l
                                                       └──Pattern:
                                                          └──Type expr: Mu
                                                             └──Variable: a6571
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a6570
                                                                         └──Type expr: Variable: a6571
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: a6576
                                                          └──Desc: Variable: r
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Mu
                                                          └──Variable: a6551
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a6570
                                                                      └──Type expr: Variable: a6551
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: a6556
                                                       └──Type expr: Mu
                                                          └──Variable: a6571
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a6570
                                                                      └──Type expr: Variable: a6571
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: a6576
                                                    └──Desc: If
                                                       └──Expression:
                                                          └──Type expr: Constructor: bool
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: a6570
                                                                   └──Type expr: Constructor: bool
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Variable: a6570
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Mu
                                                                └──Variable: a6551
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a6570
                                                                            └──Type expr: Variable: a6551
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a6556
                                                             └──Type expr: Mu
                                                                └──Variable: a6571
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a6570
                                                                            └──Type expr: Variable: a6571
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a6576
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Mu
                                                                   └──Variable: a6551
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a6570
                                                                               └──Type expr: Variable: a6551
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: a6556
                                                                └──Desc: Variant
                                                                   └──Variant description:
                                                                      └──Tag: Cons
                                                                      └──Variant row:
                                                                         └──Type expr: Mu
                                                                            └──Variable: a6500
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a6570
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Variable: a6500
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: a6556
                                                                   └──Expression:
                                                                      └──Type expr: Mu
                                                                         └──Variable: a6545
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a6570
                                                                            └──Type expr: Variant
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Cons
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Variable: a6545
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Nil
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Variable: a6556
                                                                      └──Desc: Tuple
                                                                         └──Expression:
                                                                            └──Type expr: Variable: a6570
                                                                            └──Desc: Variable
                                                                               └──Variable: x
                                                                         └──Expression:
                                                                            └──Type expr: Mu
                                                                               └──Variable: a6551
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: a6570
                                                                                           └──Type expr: Variable: a6551
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Nil
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Constructor: unit
                                                                                        └──Type expr: Variable: a6556
                                                                            └──Desc: Variable
                                                                               └──Variable: l
                                                             └──Expression:
                                                                └──Type expr: Mu
                                                                   └──Variable: a6571
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a6570
                                                                               └──Type expr: Variable: a6571
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: a6576
                                                                └──Desc: Variable
                                                                   └──Variable: r
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Mu
                                                                └──Variable: a6551
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a6570
                                                                            └──Type expr: Variable: a6551
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a6556
                                                             └──Type expr: Mu
                                                                └──Variable: a6571
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a6570
                                                                            └──Type expr: Variable: a6571
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a6576
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Mu
                                                                   └──Variable: a6551
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a6570
                                                                               └──Type expr: Variable: a6551
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: a6556
                                                                └──Desc: Variable
                                                                   └──Variable: l
                                                             └──Expression:
                                                                └──Type expr: Mu
                                                                   └──Variable: a6571
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a6570
                                                                               └──Type expr: Variable: a6571
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: a6576
                                                                └──Desc: Variant
                                                                   └──Variant description:
                                                                      └──Tag: Cons
                                                                      └──Variant row:
                                                                         └──Type expr: Mu
                                                                            └──Variable: a6511
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a6570
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Variable: a6511
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: a6576
                                                                   └──Expression:
                                                                      └──Type expr: Mu
                                                                         └──Variable: a6565
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a6570
                                                                            └──Type expr: Variant
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Cons
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Variable: a6565
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Nil
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Variable: a6576
                                                                      └──Desc: Tuple
                                                                         └──Expression:
                                                                            └──Type expr: Variable: a6570
                                                                            └──Desc: Variable
                                                                               └──Variable: x
                                                                         └──Expression:
                                                                            └──Type expr: Mu
                                                                               └──Variable: a6571
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: a6570
                                                                                           └──Type expr: Variable: a6571
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Nil
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Constructor: unit
                                                                                        └──Type expr: Variable: a6576
                                                                            └──Desc: Variable
                                                                               └──Variable: r
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: a6581
                      └──Type expr: Variable: a6581
                   └──Desc: Variable: id
                └──Abstraction:
                   └──Variables: a6581,a6581
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a6581
                         └──Type expr: Variable: a6581
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a6581
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: a6581
                            └──Desc: Variable
                               └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: a6597
                         └──Type expr: Variable: a6594
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: a6600
                            └──Type expr: Variable: a6597
                         └──Type expr: Arrow
                            └──Type expr: Variable: a6600
                            └──Type expr: Variable: a6594
                   └──Desc: Variable: compose
                └──Abstraction:
                   └──Variables: a6594
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: a6597
                            └──Type expr: Variable: a6594
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: a6600
                               └──Type expr: Variable: a6597
                            └──Type expr: Arrow
                               └──Type expr: Variable: a6600
                               └──Type expr: Variable: a6594
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a6597
                               └──Type expr: Variable: a6594
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a6600
                                  └──Type expr: Variable: a6597
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a6600
                                  └──Type expr: Variable: a6594
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a6600
                                     └──Type expr: Variable: a6597
                                  └──Desc: Variable: g
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a6600
                                     └──Type expr: Variable: a6594
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: a6600
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: a6594
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: a6597
                                                 └──Type expr: Variable: a6594
                                              └──Desc: Variable
                                                 └──Variable: f
                                           └──Expression:
                                              └──Type expr: Variable: a6597
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: a6600
                                                       └──Type expr: Variable: a6597
                                                    └──Desc: Variable
                                                       └──Variable: g
                                                 └──Expression:
                                                    └──Type expr: Variable: a6600
                                                    └──Desc: Variable
                                                       └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: a6619
                      └──Type expr: Arrow
                         └──Type expr: Variable: a6620
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Cons
                               └──Type expr: Constructor: present
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: a6619
                                     └──Type expr: Variable: a6620
                               └──Type expr: Variable: a6613
                   └──Desc: Variable: cons
                └──Abstraction:
                   └──Variables: a6619,a6619
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a6619
                         └──Type expr: Arrow
                            └──Type expr: Variable: a6620
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Cons
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: a6619
                                        └──Type expr: Variable: a6620
                                  └──Type expr: Variable: a6613
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a6619
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a6620
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a6619
                                           └──Type expr: Variable: a6620
                                     └──Type expr: Variable: a6613
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: a6620
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a6619
                                              └──Type expr: Variable: a6620
                                        └──Type expr: Variable: a6613
                                  └──Desc: Variant
                                     └──Variant description:
                                        └──Tag: Cons
                                        └──Variant row:
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a6619
                                                    └──Type expr: Variable: a6620
                                              └──Type expr: Variable: a6613
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a6619
                                           └──Type expr: Variable: a6620
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Variable: a6619
                                              └──Desc: Variable
                                                 └──Variable: x
                                           └──Expression:
                                              └──Type expr: Variable: a6620
                                              └──Desc: Variable
                                                 └──Variable: t
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: a6789
                         └──Type expr: Constructor: bool
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: a6789
                            └──Type expr: Arrow
                               └──Type expr: Variable: a6789
                               └──Type expr: Constructor: bool
                         └──Type expr: Arrow
                            └──Type expr: Mu
                               └──Variable: a6809
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a6789
                                           └──Type expr: Variable: a6809
                                     └──Type expr: Row cons
                                        └──Label: Nil
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                            └──Type expr: Arrow
                               └──Type expr: Mu
                                  └──Variable: a6819
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a6789
                                              └──Type expr: Variable: a6819
                                        └──Type expr: Variable: a6821
                               └──Type expr: Mu
                                  └──Variable: a6819
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a6789
                                              └──Type expr: Variable: a6819
                                        └──Type expr: Variable: a6821
                   └──Desc: Variable: sort_append
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: a6789
                            └──Type expr: Constructor: bool
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: a6789
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a6789
                                  └──Type expr: Constructor: bool
                            └──Type expr: Arrow
                               └──Type expr: Mu
                                  └──Variable: a6809
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a6789
                                              └──Type expr: Variable: a6809
                                        └──Type expr: Row cons
                                           └──Label: Nil
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                               └──Type expr: Arrow
                                  └──Type expr: Mu
                                     └──Variable: a6819
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a6789
                                                 └──Type expr: Variable: a6819
                                           └──Type expr: Variable: a6821
                                  └──Type expr: Mu
                                     └──Variable: a6819
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a6789
                                                 └──Type expr: Variable: a6819
                                           └──Type expr: Variable: a6821
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a6789
                               └──Type expr: Constructor: bool
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a6789
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a6789
                                     └──Type expr: Constructor: bool
                               └──Type expr: Arrow
                                  └──Type expr: Mu
                                     └──Variable: a6809
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a6789
                                                 └──Type expr: Variable: a6809
                                           └──Type expr: Row cons
                                              └──Label: Nil
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                                  └──Type expr: Arrow
                                     └──Type expr: Mu
                                        └──Variable: a6819
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a6789
                                                    └──Type expr: Variable: a6819
                                              └──Type expr: Variable: a6821
                                     └──Type expr: Mu
                                        └──Variable: a6819
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a6789
                                                    └──Type expr: Variable: a6819
                                              └──Type expr: Variable: a6821
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a6789
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: a6789
                                        └──Type expr: Constructor: bool
                                  └──Desc: Variable: le
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Mu
                                        └──Variable: a6809
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a6789
                                                    └──Type expr: Variable: a6809
                                              └──Type expr: Row cons
                                                 └──Label: Nil
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                     └──Type expr: Arrow
                                        └──Type expr: Mu
                                           └──Variable: a6819
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Cons
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a6789
                                                       └──Type expr: Variable: a6819
                                                 └──Type expr: Variable: a6821
                                        └──Type expr: Mu
                                           └──Variable: a6819
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Cons
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a6789
                                                       └──Type expr: Variable: a6819
                                                 └──Type expr: Variable: a6821
                                  └──Desc: Let rec
                                     └──Value bindings:
                                        └──Value binding:
                                           └──Variable: loop
                                           └──Abstraction:
                                              └──Variables: a6798
                                              └──Expression:
                                                 └──Type expr: Arrow
                                                    └──Type expr: Mu
                                                       └──Variable: a6801
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a6789
                                                                   └──Type expr: Variable: a6801
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row uniform
                                                                   └──Type expr: Constructor: absent
                                                    └──Type expr: Arrow
                                                       └──Type expr: Mu
                                                          └──Variable: a6783
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a6789
                                                                      └──Type expr: Variable: a6783
                                                                └──Type expr: Variable: a6798
                                                       └──Type expr: Mu
                                                          └──Variable: a6783
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a6789
                                                                      └──Type expr: Variable: a6783
                                                                └──Type expr: Variable: a6798
                                                 └──Desc: Function
                                                    └──Pattern:
                                                       └──Type expr: Mu
                                                          └──Variable: a6801
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a6789
                                                                      └──Type expr: Variable: a6801
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
                                                             └──Variable: a6783
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a6789
                                                                         └──Type expr: Variable: a6783
                                                                   └──Type expr: Variable: a6798
                                                          └──Type expr: Mu
                                                             └──Variable: a6783
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a6789
                                                                         └──Type expr: Variable: a6783
                                                                   └──Type expr: Variable: a6798
                                                       └──Desc: Match
                                                          └──Expression:
                                                             └──Type expr: Mu
                                                                └──Variable: a6801
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a6789
                                                                            └──Type expr: Variable: a6801
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                                             └──Desc: Variable
                                                                └──Variable: t
                                                          └──Type expr: Mu
                                                             └──Variable: a6801
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a6789
                                                                         └──Type expr: Variable: a6801
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
                                                                                  └──Variable: a6721
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a6789
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Variable: a6721
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
                                                                                        └──Variable: a6721
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: a6789
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Variable: a6721
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
                                                                         └──Variable: a6783
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a6789
                                                                                     └──Type expr: Variable: a6783
                                                                               └──Type expr: Variable: a6798
                                                                      └──Type expr: Mu
                                                                         └──Variable: a6783
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a6789
                                                                                     └──Type expr: Variable: a6783
                                                                               └──Type expr: Variable: a6798
                                                                   └──Desc: Variable
                                                                      └──Variable: id
                                                                      └──Type expr: Mu
                                                                         └──Variable: a6783
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a6789
                                                                                     └──Type expr: Variable: a6783
                                                                               └──Type expr: Variable: a6798
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
                                                                                  └──Variable: a6721
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a6789
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Variable: a6721
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
                                                                                        └──Variable: a6721
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: a6789
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Variable: a6721
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
                                                                            └──Variable: a6721
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a6789
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Variable: a6721
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Nil
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Constructor: unit
                                                                                        └──Type expr: Row uniform
                                                                                           └──Type expr: Constructor: absent
                                                                         └──Desc: Tuple
                                                                            └──Pattern:
                                                                               └──Type expr: Variable: a6789
                                                                               └──Desc: Any
                                                                            └──Pattern:
                                                                               └──Type expr: Mu
                                                                                  └──Variable: a6801
                                                                                  └──Type expr: Variant
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Cons
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Variable: a6789
                                                                                              └──Type expr: Variable: a6801
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
                                                                         └──Variable: a6783
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a6789
                                                                                     └──Type expr: Variable: a6783
                                                                               └──Type expr: Variable: a6798
                                                                      └──Type expr: Mu
                                                                         └──Variable: a6783
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a6789
                                                                                     └──Type expr: Variable: a6783
                                                                               └──Type expr: Variable: a6798
                                                                   └──Desc: Let
                                                                      └──Value bindings:
                                                                         └──Value binding:
                                                                            └──Pattern:
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: a6789
                                                                                  └──Type expr: Mu
                                                                                     └──Variable: a6801
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Variable: a6789
                                                                                                 └──Type expr: Variable: a6801
                                                                                           └──Type expr: Row cons
                                                                                              └──Label: Nil
                                                                                              └──Type expr: Constructor: present
                                                                                                 └──Type expr: Constructor: unit
                                                                                              └──Type expr: Row uniform
                                                                                                 └──Type expr: Constructor: absent
                                                                               └──Desc: Tuple
                                                                                  └──Pattern:
                                                                                     └──Type expr: Variable: a6789
                                                                                     └──Desc: Variable: pivot
                                                                                  └──Pattern:
                                                                                     └──Type expr: Mu
                                                                                        └──Variable: a6801
                                                                                        └──Type expr: Variant
                                                                                           └──Type expr: Row cons
                                                                                              └──Label: Cons
                                                                                              └──Type expr: Constructor: present
                                                                                                 └──Type expr: Tuple
                                                                                                    └──Type expr: Variable: a6789
                                                                                                    └──Type expr: Variable: a6801
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
                                                                                     └──Type expr: Variable: a6789
                                                                                     └──Type expr: Mu
                                                                                        └──Variable: a6801
                                                                                        └──Type expr: Variant
                                                                                           └──Type expr: Row cons
                                                                                              └──Label: Cons
                                                                                              └──Type expr: Constructor: present
                                                                                                 └──Type expr: Tuple
                                                                                                    └──Type expr: Variable: a6789
                                                                                                    └──Type expr: Variable: a6801
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
                                                                                              └──Type expr: Variable: a6789
                                                                                              └──Type expr: Constructor: bool
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Variable: a6789
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: a6801
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: a6789
                                                                                                             └──Type expr: Variable: a6801
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
                                                                                                    └──Variable: a6801
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a6789
                                                                                                                └──Type expr: Variable: a6801
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Nil
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Constructor: unit
                                                                                                             └──Type expr: Row uniform
                                                                                                                └──Type expr: Constructor: absent
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Variable: a6789
                                                                                                       └──Type expr: Constructor: bool
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: a6789
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: a6801
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: a6789
                                                                                                                      └──Type expr: Variable: a6801
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Nil
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Constructor: unit
                                                                                                                   └──Type expr: Row uniform
                                                                                                                      └──Type expr: Constructor: absent
                                                                                              └──Desc: Variable
                                                                                                 └──Variable: select
                                                                                                 └──Type expr: Variable: a6789
                                                                                           └──Expression:
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: a6801
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: a6789
                                                                                                             └──Type expr: Variable: a6801
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
                                                                                           └──Type expr: Variable: a6789
                                                                                           └──Type expr: Constructor: bool
                                                                                        └──Desc: Variable
                                                                                           └──Variable: f
                                                                      └──Expression:
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Mu
                                                                               └──Variable: a6783
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: a6789
                                                                                           └──Type expr: Variable: a6783
                                                                                     └──Type expr: Variable: a6798
                                                                            └──Type expr: Mu
                                                                               └──Variable: a6783
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: a6789
                                                                                           └──Type expr: Variable: a6783
                                                                                     └──Type expr: Variable: a6798
                                                                         └──Desc: Let
                                                                            └──Value bindings:
                                                                               └──Value binding:
                                                                                  └──Pattern:
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Mu
                                                                                           └──Variable: a6801
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: a6789
                                                                                                       └──Type expr: Variable: a6801
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Nil
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Constructor: unit
                                                                                                    └──Type expr: Row uniform
                                                                                                       └──Type expr: Constructor: absent
                                                                                        └──Type expr: Mu
                                                                                           └──Variable: a6801
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: a6789
                                                                                                       └──Type expr: Variable: a6801
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Nil
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Constructor: unit
                                                                                                    └──Type expr: Row uniform
                                                                                                       └──Type expr: Constructor: absent
                                                                                     └──Desc: Tuple
                                                                                        └──Pattern:
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: a6801
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: a6789
                                                                                                          └──Type expr: Variable: a6801
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Nil
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Constructor: unit
                                                                                                       └──Type expr: Row uniform
                                                                                                          └──Type expr: Constructor: absent
                                                                                           └──Desc: Variable: l
                                                                                        └──Pattern:
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: a6801
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: a6789
                                                                                                          └──Type expr: Variable: a6801
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
                                                                                              └──Variable: a6801
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: a6789
                                                                                                          └──Type expr: Variable: a6801
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Nil
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Constructor: unit
                                                                                                       └──Type expr: Row uniform
                                                                                                          └──Type expr: Constructor: absent
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: a6801
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: a6789
                                                                                                          └──Type expr: Variable: a6801
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
                                                                                                    └──Type expr: Variable: a6789
                                                                                                    └──Type expr: Constructor: bool
                                                                                                 └──Type expr: Tuple
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a6801
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a6789
                                                                                                                   └──Type expr: Variable: a6801
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Nil
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Constructor: unit
                                                                                                                └──Type expr: Row uniform
                                                                                                                   └──Type expr: Constructor: absent
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a6801
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a6789
                                                                                                                   └──Type expr: Variable: a6801
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
                                                                                                          └──Variable: a6801
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: a6789
                                                                                                                      └──Type expr: Variable: a6801
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Nil
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Constructor: unit
                                                                                                                   └──Type expr: Row uniform
                                                                                                                      └──Type expr: Constructor: absent
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Arrow
                                                                                                             └──Type expr: Variable: a6789
                                                                                                             └──Type expr: Constructor: bool
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Mu
                                                                                                                └──Variable: a6801
                                                                                                                └──Type expr: Variant
                                                                                                                   └──Type expr: Row cons
                                                                                                                      └──Label: Cons
                                                                                                                      └──Type expr: Constructor: present
                                                                                                                         └──Type expr: Tuple
                                                                                                                            └──Type expr: Variable: a6789
                                                                                                                            └──Type expr: Variable: a6801
                                                                                                                      └──Type expr: Row cons
                                                                                                                         └──Label: Nil
                                                                                                                         └──Type expr: Constructor: present
                                                                                                                            └──Type expr: Constructor: unit
                                                                                                                         └──Type expr: Row uniform
                                                                                                                            └──Type expr: Constructor: absent
                                                                                                             └──Type expr: Mu
                                                                                                                └──Variable: a6801
                                                                                                                └──Type expr: Variant
                                                                                                                   └──Type expr: Row cons
                                                                                                                      └──Label: Cons
                                                                                                                      └──Type expr: Constructor: present
                                                                                                                         └──Type expr: Tuple
                                                                                                                            └──Type expr: Variable: a6789
                                                                                                                            └──Type expr: Variable: a6801
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
                                                                                                       └──Variable: a6801
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a6789
                                                                                                                   └──Type expr: Variable: a6801
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
                                                                                                 └──Type expr: Variable: a6789
                                                                                                 └──Type expr: Constructor: bool
                                                                                              └──Desc: Function
                                                                                                 └──Pattern:
                                                                                                    └──Type expr: Variable: a6789
                                                                                                    └──Desc: Variable: y
                                                                                                 └──Expression:
                                                                                                    └──Type expr: Constructor: bool
                                                                                                    └──Desc: Application
                                                                                                       └──Expression:
                                                                                                          └──Type expr: Arrow
                                                                                                             └──Type expr: Variable: a6789
                                                                                                             └──Type expr: Constructor: bool
                                                                                                          └──Desc: Application
                                                                                                             └──Expression:
                                                                                                                └──Type expr: Arrow
                                                                                                                   └──Type expr: Variable: a6789
                                                                                                                   └──Type expr: Arrow
                                                                                                                      └──Type expr: Variable: a6789
                                                                                                                      └──Type expr: Constructor: bool
                                                                                                                └──Desc: Variable
                                                                                                                   └──Variable: le
                                                                                                             └──Expression:
                                                                                                                └──Type expr: Variable: a6789
                                                                                                                └──Desc: Variable
                                                                                                                   └──Variable: y
                                                                                                       └──Expression:
                                                                                                          └──Type expr: Variable: a6789
                                                                                                          └──Desc: Variable
                                                                                                             └──Variable: pivot
                                                                            └──Expression:
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Mu
                                                                                     └──Variable: a6783
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Variable: a6789
                                                                                                 └──Type expr: Variable: a6783
                                                                                           └──Type expr: Variable: a6798
                                                                                  └──Type expr: Mu
                                                                                     └──Variable: a6783
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Variable: a6789
                                                                                                 └──Type expr: Variable: a6783
                                                                                           └──Type expr: Variable: a6798
                                                                               └──Desc: Application
                                                                                  └──Expression:
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: a6783
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: a6789
                                                                                                          └──Type expr: Variable: a6783
                                                                                                    └──Type expr: Variable: a6798
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: a6783
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: a6789
                                                                                                          └──Type expr: Variable: a6783
                                                                                                    └──Type expr: Variable: a6798
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: a6783
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: a6789
                                                                                                          └──Type expr: Variable: a6783
                                                                                                    └──Type expr: Variable: a6798
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: a6783
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: a6789
                                                                                                          └──Type expr: Variable: a6783
                                                                                                    └──Type expr: Variable: a6798
                                                                                     └──Desc: Application
                                                                                        └──Expression:
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: a6783
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a6789
                                                                                                                └──Type expr: Variable: a6783
                                                                                                          └──Type expr: Variable: a6798
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: a6783
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a6789
                                                                                                                └──Type expr: Variable: a6783
                                                                                                          └──Type expr: Variable: a6798
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a6783
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a6789
                                                                                                                   └──Type expr: Variable: a6783
                                                                                                             └──Type expr: Variable: a6798
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a6783
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a6789
                                                                                                                   └──Type expr: Variable: a6783
                                                                                                             └──Type expr: Variable: a6798
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a6783
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a6789
                                                                                                                   └──Type expr: Variable: a6783
                                                                                                             └──Type expr: Variable: a6798
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a6783
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a6789
                                                                                                                   └──Type expr: Variable: a6783
                                                                                                             └──Type expr: Variable: a6798
                                                                                           └──Desc: Variable
                                                                                              └──Variable: compose
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: a6783
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: a6789
                                                                                                             └──Type expr: Variable: a6783
                                                                                                       └──Type expr: Variable: a6798
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: a6783
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: a6789
                                                                                                             └──Type expr: Variable: a6783
                                                                                                       └──Type expr: Variable: a6798
                                                                                        └──Expression:
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: a6783
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: a6789
                                                                                                             └──Type expr: Variable: a6783
                                                                                                       └──Type expr: Variable: a6798
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: a6783
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: a6789
                                                                                                             └──Type expr: Variable: a6783
                                                                                                       └──Type expr: Variable: a6798
                                                                                           └──Desc: Application
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a6801
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a6789
                                                                                                                   └──Type expr: Variable: a6801
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Nil
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Constructor: unit
                                                                                                                └──Type expr: Row uniform
                                                                                                                   └──Type expr: Constructor: absent
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: a6783
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: a6789
                                                                                                                      └──Type expr: Variable: a6783
                                                                                                                └──Type expr: Variable: a6798
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: a6783
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: a6789
                                                                                                                      └──Type expr: Variable: a6783
                                                                                                                └──Type expr: Variable: a6798
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: loop
                                                                                              └──Expression:
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: a6801
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a6789
                                                                                                                └──Type expr: Variable: a6801
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
                                                                                           └──Variable: a6783
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: a6789
                                                                                                       └──Type expr: Variable: a6783
                                                                                                 └──Type expr: Variable: a6798
                                                                                        └──Type expr: Mu
                                                                                           └──Variable: a6783
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: a6789
                                                                                                       └──Type expr: Variable: a6783
                                                                                                 └──Type expr: Variable: a6798
                                                                                     └──Desc: Application
                                                                                        └──Expression:
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: a6783
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a6789
                                                                                                                └──Type expr: Variable: a6783
                                                                                                          └──Type expr: Variable: a6798
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: a6783
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a6789
                                                                                                                └──Type expr: Variable: a6783
                                                                                                          └──Type expr: Variable: a6798
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: a6783
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a6789
                                                                                                                └──Type expr: Variable: a6783
                                                                                                          └──Type expr: Variable: a6798
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: a6783
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a6789
                                                                                                                └──Type expr: Variable: a6783
                                                                                                          └──Type expr: Variable: a6798
                                                                                           └──Desc: Application
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: a6783
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: a6789
                                                                                                                      └──Type expr: Variable: a6783
                                                                                                                └──Type expr: Variable: a6798
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: a6783
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: a6789
                                                                                                                      └──Type expr: Variable: a6783
                                                                                                                └──Type expr: Variable: a6798
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Mu
                                                                                                             └──Variable: a6783
                                                                                                             └──Type expr: Variant
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Cons
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Tuple
                                                                                                                         └──Type expr: Variable: a6789
                                                                                                                         └──Type expr: Variable: a6783
                                                                                                                   └──Type expr: Variable: a6798
                                                                                                          └──Type expr: Mu
                                                                                                             └──Variable: a6783
                                                                                                             └──Type expr: Variant
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Cons
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Tuple
                                                                                                                         └──Type expr: Variable: a6789
                                                                                                                         └──Type expr: Variable: a6783
                                                                                                                   └──Type expr: Variable: a6798
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Mu
                                                                                                             └──Variable: a6783
                                                                                                             └──Type expr: Variant
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Cons
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Tuple
                                                                                                                         └──Type expr: Variable: a6789
                                                                                                                         └──Type expr: Variable: a6783
                                                                                                                   └──Type expr: Variable: a6798
                                                                                                          └──Type expr: Mu
                                                                                                             └──Variable: a6783
                                                                                                             └──Type expr: Variant
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Cons
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Tuple
                                                                                                                         └──Type expr: Variable: a6789
                                                                                                                         └──Type expr: Variable: a6783
                                                                                                                   └──Type expr: Variable: a6798
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: compose
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a6783
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a6789
                                                                                                                   └──Type expr: Variable: a6783
                                                                                                             └──Type expr: Variable: a6798
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a6783
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a6789
                                                                                                                   └──Type expr: Variable: a6783
                                                                                                             └──Type expr: Variable: a6798
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a6783
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a6789
                                                                                                                   └──Type expr: Variable: a6783
                                                                                                             └──Type expr: Variable: a6798
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a6783
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a6789
                                                                                                                   └──Type expr: Variable: a6783
                                                                                                             └──Type expr: Variable: a6798
                                                                                                 └──Desc: Application
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Variable: a6789
                                                                                                          └──Type expr: Arrow
                                                                                                             └──Type expr: Mu
                                                                                                                └──Variable: a6783
                                                                                                                └──Type expr: Variant
                                                                                                                   └──Type expr: Row cons
                                                                                                                      └──Label: Cons
                                                                                                                      └──Type expr: Constructor: present
                                                                                                                         └──Type expr: Tuple
                                                                                                                            └──Type expr: Variable: a6789
                                                                                                                            └──Type expr: Variable: a6783
                                                                                                                      └──Type expr: Variable: a6798
                                                                                                             └──Type expr: Mu
                                                                                                                └──Variable: a6783
                                                                                                                └──Type expr: Variant
                                                                                                                   └──Type expr: Row cons
                                                                                                                      └──Label: Cons
                                                                                                                      └──Type expr: Constructor: present
                                                                                                                         └──Type expr: Tuple
                                                                                                                            └──Type expr: Variable: a6789
                                                                                                                            └──Type expr: Variable: a6783
                                                                                                                      └──Type expr: Variable: a6798
                                                                                                       └──Desc: Variable
                                                                                                          └──Variable: cons
                                                                                                          └──Type expr: Mu
                                                                                                             └──Variable: a6783
                                                                                                             └──Type expr: Variant
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Cons
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Tuple
                                                                                                                         └──Type expr: Variable: a6789
                                                                                                                         └──Type expr: Variable: a6783
                                                                                                                   └──Type expr: Variable: a6798
                                                                                                          └──Type expr: Variable: a6789
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Variable: a6789
                                                                                                       └──Desc: Variable
                                                                                                          └──Variable: pivot
                                                                                        └──Expression:
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: a6783
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: a6789
                                                                                                             └──Type expr: Variable: a6783
                                                                                                       └──Type expr: Variable: a6798
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: a6783
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: a6789
                                                                                                             └──Type expr: Variable: a6783
                                                                                                       └──Type expr: Variable: a6798
                                                                                           └──Desc: Application
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a6801
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a6789
                                                                                                                   └──Type expr: Variable: a6801
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Nil
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Constructor: unit
                                                                                                                └──Type expr: Row uniform
                                                                                                                   └──Type expr: Constructor: absent
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: a6783
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: a6789
                                                                                                                      └──Type expr: Variable: a6783
                                                                                                                └──Type expr: Variable: a6798
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: a6783
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: a6789
                                                                                                                      └──Type expr: Variable: a6783
                                                                                                                └──Type expr: Variable: a6798
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: loop
                                                                                              └──Expression:
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: a6801
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a6789
                                                                                                                └──Type expr: Variable: a6801
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
                                              └──Variable: a6809
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Cons
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a6789
                                                          └──Type expr: Variable: a6809
                                                    └──Type expr: Row cons
                                                       └──Label: Nil
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row uniform
                                                          └──Type expr: Constructor: absent
                                           └──Type expr: Arrow
                                              └──Type expr: Mu
                                                 └──Variable: a6819
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a6789
                                                             └──Type expr: Variable: a6819
                                                       └──Type expr: Variable: a6821
                                              └──Type expr: Mu
                                                 └──Variable: a6819
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a6789
                                                             └──Type expr: Variable: a6819
                                                       └──Type expr: Variable: a6821
                                        └──Desc: Variable
                                           └──Variable: loop
                                           └──Type expr: Variable: a6821
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Mu
                         └──Variable: a6836
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Cons
                               └──Type expr: Constructor: present
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: a6847
                                     └──Type expr: Variable: a6836
                               └──Type expr: Row cons
                                  └──Label: Nil
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: a6847
                            └──Type expr: Arrow
                               └──Type expr: Variable: a6847
                               └──Type expr: Constructor: bool
                         └──Type expr: Mu
                            └──Variable: a6830
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Cons
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: a6847
                                        └──Type expr: Variable: a6830
                                  └──Type expr: Row cons
                                     └──Label: Nil
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Variable: a6886
                   └──Desc: Variable: sort
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Mu
                            └──Variable: a6836
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Cons
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: a6847
                                        └──Type expr: Variable: a6836
                                  └──Type expr: Row cons
                                     └──Label: Nil
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: a6847
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a6847
                                  └──Type expr: Constructor: bool
                            └──Type expr: Mu
                               └──Variable: a6830
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a6847
                                           └──Type expr: Variable: a6830
                                     └──Type expr: Row cons
                                        └──Label: Nil
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Variable: a6886
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Mu
                               └──Variable: a6836
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a6847
                                           └──Type expr: Variable: a6836
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
                                  └──Type expr: Variable: a6847
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a6847
                                     └──Type expr: Constructor: bool
                               └──Type expr: Mu
                                  └──Variable: a6830
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a6847
                                              └──Type expr: Variable: a6830
                                        └──Type expr: Row cons
                                           └──Label: Nil
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: a6886
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a6847
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: a6847
                                        └──Type expr: Constructor: bool
                                  └──Desc: Variable: le
                               └──Expression:
                                  └──Type expr: Mu
                                     └──Variable: a6830
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a6847
                                                 └──Type expr: Variable: a6830
                                           └──Type expr: Row cons
                                              └──Label: Nil
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Variable: a6886
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Mu
                                              └──Variable: a6830
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Cons
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a6847
                                                          └──Type expr: Variable: a6830
                                                    └──Type expr: Row cons
                                                       └──Label: Nil
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Variable: a6886
                                           └──Type expr: Mu
                                              └──Variable: a6830
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Cons
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a6847
                                                          └──Type expr: Variable: a6830
                                                    └──Type expr: Row cons
                                                       └──Label: Nil
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Variable: a6886
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Mu
                                                    └──Variable: a6836
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a6847
                                                                └──Type expr: Variable: a6836
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                                 └──Type expr: Arrow
                                                    └──Type expr: Mu
                                                       └──Variable: a6830
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a6847
                                                                   └──Type expr: Variable: a6830
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a6886
                                                    └──Type expr: Mu
                                                       └──Variable: a6830
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a6847
                                                                   └──Type expr: Variable: a6830
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a6886
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: a6847
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a6847
                                                             └──Type expr: Constructor: bool
                                                       └──Type expr: Arrow
                                                          └──Type expr: Mu
                                                             └──Variable: a6836
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a6847
                                                                         └──Type expr: Variable: a6836
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                          └──Type expr: Arrow
                                                             └──Type expr: Mu
                                                                └──Variable: a6830
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a6847
                                                                            └──Type expr: Variable: a6830
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a6886
                                                             └──Type expr: Mu
                                                                └──Variable: a6830
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a6847
                                                                            └──Type expr: Variable: a6830
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a6886
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a6847
                                                                └──Type expr: Constructor: bool
                                                             └──Type expr: Arrow
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: a6847
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: a6847
                                                                      └──Type expr: Constructor: bool
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Mu
                                                                      └──Variable: a6836
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: a6847
                                                                                  └──Type expr: Variable: a6836
                                                                            └──Type expr: Row cons
                                                                               └──Label: Nil
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row uniform
                                                                                  └──Type expr: Constructor: absent
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Mu
                                                                         └──Variable: a6830
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a6847
                                                                                     └──Type expr: Variable: a6830
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: a6886
                                                                      └──Type expr: Mu
                                                                         └──Variable: a6830
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a6847
                                                                                     └──Type expr: Variable: a6830
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: a6886
                                                          └──Desc: Variable
                                                             └──Variable: sort_append
                                                             └──Type expr: Variable: a6847
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a6847
                                                             └──Type expr: Constructor: bool
                                                          └──Desc: Function
                                                             └──Pattern:
                                                                └──Type expr: Variable: a6847
                                                                └──Desc: Variable: x
                                                             └──Expression:
                                                                └──Type expr: Constructor: bool
                                                                └──Desc: Constant: true
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: a6847
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: a6847
                                                          └──Type expr: Constructor: bool
                                                    └──Desc: Variable
                                                       └──Variable: le
                                           └──Expression:
                                              └──Type expr: Mu
                                                 └──Variable: a6836
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a6847
                                                             └──Type expr: Variable: a6836
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
                                           └──Variable: a6830
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Cons
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a6847
                                                       └──Type expr: Variable: a6830
                                                 └──Type expr: Row cons
                                                    └──Label: Nil
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Variable: a6886
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Nil
                                              └──Variant row:
                                                 └──Type expr: Mu
                                                    └──Variable: a6865
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a6847
                                                             └──Type expr: Variant
                                                                └──Type expr: Variable: a6865
                                                       └──Type expr: Row cons
                                                          └──Label: Nil
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Variable: a6886 |}]