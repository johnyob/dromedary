(lang dune 2.9)

(name dromedary)

(generate_opam_files true)

(license MIT)

(maintainers "ajo41@cam.ac.uk")

(authors "Alistair O'Brien")

(source
 (github johnyob/dromedary))

(package
 (name dromedary)
 (synopsis "An experimental subset of OCaml")
 (description
  "Dromedary is an experimental subset of OCaml, using constraint-based type inference!")
 (depends
  (dune
   (>= 2.9))
  (base
   (= v0.14.1))
  (core
   (= v0.14.1))
  (core_bench
   (= v0.14.0))
  (core_unix
   (= v0.14.0))
  (ppx_jane
   (= v0.14.0))
  (ppx_sexp_conv
   (= v0.14.3))
  (ppx_compare
   (= v0.14.0))
  (ppx_deriving
   (= 5.2.1))
  (ppx_let
   (= v0.14.0))
  (vec
   (= 0.3.0))
  (logs
   (= 0.7.0))
  landmarks
  (bisect_ppx
   (= 2.6.0))
  (qcheck
   (= 0.17))
  (alcotest
   (= 1.4.0))
  (qcheck-alcotest
   (= 0.17))
  (menhir
   (= 20210419))
  (menhirLib
   (= 20210419))))

(using menhir 2.1)
