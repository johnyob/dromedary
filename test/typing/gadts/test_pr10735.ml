open! Import
open Util

let%expect_test "" =
  let str =
    {|
      type 'a t;;
      type 'a u;;

      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;

      external magic : 'a 'b. 'a -> 'b = "%magic";;

      let () = 
        let (Refl : (bool t, bool u) eq) = magic () in ()
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    "Inconsistent equations added by local branches" |}]
