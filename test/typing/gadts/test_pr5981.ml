open! Import
open Util

let%expect_test "" =
  let str =
    {|
      type 'a s_t;;

      type 'a ab = 
        | A constraint 'a = int s_t
        | B constraint 'a = float s_t
      ;;

      (* Fails bcs s_t is abstract, would pass 
         if [type 'a s_t = int (or some other type constant)] *)
      let f = 
        fun (l : int s_t ab) (r : int s_t ab) ->
          match (l, r) with
          ( (A, B) -> "f A B" )
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    "Inconsistent equations added by local branches" |}]
