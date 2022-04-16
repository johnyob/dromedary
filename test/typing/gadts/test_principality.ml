open! Import 
open Util

let%expect_test "principality-1" =
  let str = 
    {|
      type t = 
        | A
        | B
      ;;

      type 'a u = 
        | I constraint 'a = int
        | M constraint 'a = t
      ;;

      type dyn = 
        | Sigma of 'a. 'a u * 'a
      ;;

      (* Passes since we don't have exhaustive checks. 
         Implementation also lacks propagation due to treatment of rigids in implications (-1) *)
      let f = 
        fun (Sigma (M, x)) -> (match x with (A -> ()))
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
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: A
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: t
                └──Constructor declaration:
                   └──Constructor name: B
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: t
       └──Structure item: Type
          └──Type declaration:
             └──Type name: u
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: I
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: u
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: int
                └──Constructor declaration:
                   └──Constructor name: M
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: u
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: t
       └──Structure item: Type
          └──Type declaration:
             └──Type name: dyn
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Sigma
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: dyn
                   └──Constructor argument:
                      └──Constructor betas: a
                      └──Type expr: Tuple
                         └──Type expr: Constructor: u
                            └──Type expr: Variable: a
                         └──Type expr: Variable: a
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: dyn
                      └──Type expr: Constructor: unit
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: dyn
                         └──Type expr: Constructor: unit
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: dyn
                            └──Desc: Construct
                               └──Constructor description:
                                  └──Name: Sigma
                                  └──Constructor argument type:
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: u
                                           └──Type expr: Variable: a13747
                                        └──Type expr: Variable: a13747
                                  └──Constructor type:
                                     └──Type expr: Constructor: dyn
                               └──Pattern:
                                  └──Type expr: Tuple
                                     └──Type expr: Constructor: u
                                        └──Type expr: Variable: a13747
                                     └──Type expr: Variable: a13747
                                  └──Desc: Tuple
                                     └──Pattern:
                                        └──Type expr: Constructor: u
                                           └──Type expr: Variable: a13747
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: M
                                              └──Constructor type:
                                                 └──Type expr: Constructor: u
                                                    └──Type expr: Variable: a13747
                                     └──Pattern:
                                        └──Type expr: Variable: a13747
                                        └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: unit
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Variable: a13747
                                  └──Desc: Variable
                                     └──Variable: x
                               └──Type expr: Variable: a13747
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variable: a13747
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: A
                                              └──Constructor type:
                                                 └──Type expr: Variable: a13747
                                     └──Expression:
                                        └──Type expr: Constructor: unit
                                        └──Desc: Constant: () |}]

let%expect_test "principality-2" =
  let str = 
    {|
      type 'a t = 
        | Int constraint 'a = int
        | Bool constraint 'a = bool
      ;;
      
      external ignore : 'a. 'a -> unit = "%ignore";;

      let (type 'a) f = 
        fun t (x : 'a) ->
          ( ignore (t : 'a t);
          match (t, x) with
          ( (Int, n) -> n + 1
          | (Bool, b) -> 1
          ))
      ;;
    |}
  in
  print_infer_result str;
  [%expect {| ("Type escape it's equational scope" (type_expr ((desc (Ttyp_var a128))))) |}]

let%expect_test "principality-3" =
  let str = 
    {|
      type 'a t = 
        | Int constraint 'a = int
        | Bool constraint 'a = bool
      ;;
      
      external ignore : 'a. 'a -> unit = "%ignore";;

      let (type 'a) f = 
        fun t (x : 'a) ->
          ignore (t : 'a t);
          match (t, x) with
          ( (Int, n) -> n + 1
          | _ -> 1
          )
      ;;  
    |}
  in
  print_infer_result str;
  [%expect {| ("Type escape it's equational scope" (type_expr ((desc (Ttyp_var a129))))) |}]

let%expect_test "principality-4" =
  let str = 
    {|
      type 'a t = 
        | Int constraint 'a = int
        | Bool constraint 'a = bool
      ;;
      
      external ignore : 'a. 'a -> unit = "%ignore";;

      let (type 'a) f = 
        fun t (x : 'a) ->
          ignore (match (t, x) with
            ( (Int, n) -> n + 1
            | (Bool, b) -> 1
            ));
          ignore (t : 'a t)
      ;;
    |}
  in
  print_infer_result str;
  [%expect {| "Non rigid equations" |}]


let%expect_test "principality-5" =
  let str = 
    {|
      type 'a t = 
        | Int constraint 'a = int
        | Bool constraint 'a = bool
      ;;
      
      external ignore : 'a. 'a -> unit = "%ignore";;

      let (type 'a) f = 
        fun t (x : 'a) ->
          ignore (match (t, x) with
            ( (Int, n) -> n + 1
            | _ -> 1
            ));
          ignore (t : 'a t)
      ;;
    |}
  in
  print_infer_result str;
  [%expect {| "Non rigid equations" |}]

let%expect_test "principality-6" =
  let str = 
    {|
      type 'a ab = A | B;;

      (* Hidden by module, but alias test cases are still useful here *)
      type 'a mab = 'a ab;;
      type 'a t = 
        | Ab constraint 'a = unit ab
        | Mab constraint 'a = unit mab
      ;;

      let f1 = 
        fun t ->
          match t with
          ( Ab -> true
          | Mab -> false
          )
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    "Non rigid equations" |}]


let%expect_test "principality-7" =
  let str = 
    {|
      type 'a ab = A | B;;

      (* Hidden by module, but alias test cases are still useful here *)
      type 'a mab = 'a ab;;
      type 'a t = 
        | Ab constraint 'a = unit ab
        | Mab constraint 'a = unit mab
      ;;

      (* Passes bcs no modules *)
      let (type 'a) f2 = 
        fun (t : 'a t) ->
          match t with
          ( Ab -> true
          | Mab -> false
          )
      ;;

      let f3 = 
        fun (t : unit ab t) ->
          match t with
          ( Ab -> true
          | Mab -> false
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
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a13984
                      └──Type expr: Constructor: bool
                   └──Desc: Variable: f2
                └──Abstraction:
                   └──Variables: a13984
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: a13984
                         └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: a13984
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: bool
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: a13984
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: a13984
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: a13984
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Ab
                                              └──Constructor type:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: a13984
                                     └──Expression:
                                        └──Type expr: Constructor: bool
                                        └──Desc: Constant: true
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: a13984
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Mab
                                              └──Constructor type:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: a13984
                                     └──Expression:
                                        └──Type expr: Constructor: bool
                                        └──Desc: Constant: false
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Constructor: ab
                            └──Type expr: Constructor: unit
                      └──Type expr: Constructor: bool
                   └──Desc: Variable: f3
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Constructor: ab
                               └──Type expr: Constructor: unit
                         └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Constructor: ab
                                  └──Type expr: Constructor: unit
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: bool
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Constructor: ab
                                        └──Type expr: Constructor: unit
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: t
                                  └──Type expr: Constructor: ab
                                     └──Type expr: Constructor: unit
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
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
                                     └──Expression:
                                        └──Type expr: Constructor: bool
                                        └──Desc: Constant: true
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Constructor: ab
                                              └──Type expr: Constructor: unit
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Mab
                                              └──Constructor type:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Constructor: ab
                                                       └──Type expr: Constructor: unit
                                     └──Expression:
                                        └──Type expr: Constructor: bool
                                        └──Desc: Constant: false |}]

let%expect_test "principality-8" =
  let str = 
    {|
      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;

      let (type 'a) g1 = 
        fun (eq : ('a, int option) eq) (x : 'a) ->
          (match eq with ( Refl -> x ) : int option)
      ;;

      external ignore : 'a. 'a -> unit = "%ignore";;

      (* Unclear why OCaml doesn't pass this test. I suspect it's bcs inference treats _ 
         differently *)
      let (type 'a) g1 = 
        exists (type 'b) ->
          fun (eq : ('a, 'b option) eq) (x : 'a) ->
            ignore (eq : ('a, int option) eq);
            (match eq with ( Refl -> x ) : int option)
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
                   └──Constructor alphas: a b
                   └──Constructor type:
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Variable: b
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: a14046
                         └──Type expr: Constructor: option
                            └──Type expr: Constructor: int
                      └──Type expr: Arrow
                         └──Type expr: Variable: a14046
                         └──Type expr: Constructor: option
                            └──Type expr: Constructor: int
                   └──Desc: Variable: g1
                └──Abstraction:
                   └──Variables: a14046
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: a14046
                            └──Type expr: Constructor: option
                               └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Variable: a14046
                            └──Type expr: Constructor: option
                               └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: a14046
                               └──Type expr: Constructor: option
                                  └──Type expr: Constructor: int
                            └──Desc: Variable: eq
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a14046
                               └──Type expr: Constructor: option
                                  └──Type expr: Constructor: int
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: a14046
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Constructor: option
                                     └──Type expr: Constructor: int
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: a14046
                                           └──Type expr: Constructor: option
                                              └──Type expr: Constructor: int
                                        └──Desc: Variable
                                           └──Variable: eq
                                     └──Type expr: Constructor: eq
                                        └──Type expr: Variable: a14046
                                        └──Type expr: Constructor: option
                                           └──Type expr: Constructor: int
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a14046
                                                 └──Type expr: Constructor: option
                                                    └──Type expr: Constructor: int
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Refl
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a14046
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: int
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: x
       └──Structure item: Primitive
          └──Value description:
             └──Name: ignore
             └──Scheme:
                └──Variables: a14086
                └──Type expr: Arrow
                   └──Type expr: Variable: a14086
                   └──Type expr: Constructor: unit
             └──Primitive name: %ignore
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: a14104
                         └──Type expr: Constructor: option
                            └──Type expr: Constructor: int
                      └──Type expr: Arrow
                         └──Type expr: Variable: a14104
                         └──Type expr: Constructor: option
                            └──Type expr: Constructor: int
                   └──Desc: Variable: g1
                └──Abstraction:
                   └──Variables: a14104
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: a14104
                            └──Type expr: Constructor: option
                               └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Variable: a14104
                            └──Type expr: Constructor: option
                               └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: a14104
                               └──Type expr: Constructor: option
                                  └──Type expr: Constructor: int
                            └──Desc: Variable: eq
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a14104
                               └──Type expr: Constructor: option
                                  └──Type expr: Constructor: int
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: a14104
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Constructor: option
                                     └──Type expr: Constructor: int
                                  └──Desc: Sequence
                                     └──Expression:
                                        └──Type expr: Constructor: unit
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: eq
                                                    └──Type expr: Variable: a14104
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: unit
                                              └──Desc: Variable
                                                 └──Variable: ignore
                                                 └──Type expr: Constructor: eq
                                                    └──Type expr: Variable: a14104
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: int
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a14104
                                                 └──Type expr: Constructor: option
                                                    └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: eq
                                     └──Expression:
                                        └──Type expr: Constructor: option
                                           └──Type expr: Constructor: int
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a14104
                                                 └──Type expr: Constructor: option
                                                    └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: eq
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: a14104
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: int
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: a14104
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: int
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Refl
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: a14104
                                                                └──Type expr: Constructor: option
                                                                   └──Type expr: Constructor: int
                                                 └──Expression:
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: x |}]

let%expect_test "principality-9" =
  let str = 
    {|
      type foo = int;;
      type 'a gadt = 
        | F constraint 'a = foo
      ;;

      type 'a t = { a: 'a; b : 'a gadt };;

      (* Associated let patterns not supported -- lack of record pattern matching *)
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: foo
             └──Type declaration kind: Alias
                └──Alias
                   └──Alias name: foo
                   └──Alias alphas:
                   └──Type expr: Constructor: int
       └──Structure item: Type
          └──Type declaration:
             └──Type name: gadt
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: F
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: gadt
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: foo
       └──Structure item: Type
          └──Type declaration:
             └──Type name: t
             └──Type declaration kind: Record
                └──Label declaration:
                   └──Label name: a
                   └──Label alphas: a
                   └──Label betas:
                   └──Type expr: Variable: a
                   └──Type expr: Constructor: t
                      └──Type expr: Variable: a
                └──Label declaration:
                   └──Label name: b
                   └──Label alphas: a
                   └──Label betas:
                   └──Type expr: Constructor: gadt
                      └──Type expr: Variable: a
                   └──Type expr: Constructor: t
                      └──Type expr: Variable: a |}]

let%expect_test "principality-10" =
  let str = 
    {|
      type foo = int;;

      type ('a, 'b, 'c) eq3 = 
        | Refl constraint 'a = 'b and 'a = 'c
      ;;

      type 'a t = { a : 'a; b : (int, foo, 'a) eq3 };;

      
      (* Associated let patterns not supported -- lack of record pattern matching *)
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: foo
             └──Type declaration kind: Alias
                └──Alias
                   └──Alias name: foo
                   └──Alias alphas:
                   └──Type expr: Constructor: int
       └──Structure item: Type
          └──Type declaration:
             └──Type name: eq3
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Refl
                   └──Constructor alphas: a b c
                   └──Constructor type:
                      └──Type expr: Constructor: eq3
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
                         └──Type expr: Variable: c
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Variable: b
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Variable: c
       └──Structure item: Type
          └──Type declaration:
             └──Type name: t
             └──Type declaration kind: Record
                └──Label declaration:
                   └──Label name: a
                   └──Label alphas: a
                   └──Label betas:
                   └──Type expr: Variable: a
                   └──Type expr: Constructor: t
                      └──Type expr: Variable: a
                └──Label declaration:
                   └──Label name: b
                   └──Label alphas: a
                   └──Label betas:
                   └──Type expr: Constructor: eq3
                      └──Type expr: Constructor: int
                      └──Type expr: Constructor: foo
                      └──Type expr: Variable: a
                   └──Type expr: Constructor: t
                      └──Type expr: Variable: a |}]
