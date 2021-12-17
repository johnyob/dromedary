let () =
  let open Alcotest in
  run "Constraints" (Test_union_find.tests @ Test_unifier.tests)
