{
  pkgs ? import <nixpkgs> {},
  ocamlPackages ? pkgs.ocaml-ng.ocamlPackages_5_2,
}: let
  inherit (pkgs) ocamlPackages;
in
  with ocamlPackages;
    buildDunePackage rec {
      pname = "dromedary";
      version = "dev";
      src = ./.;

      nativeBuildInputs = [
        menhir
        odoc
        dune
      ];

      propagatedBuildInputs = [
        base
        core
        core_bench
        core_unix
        ppx_jane
        ppx_sexp_conv
        ppx_compare
        ppx_deriving
        ppx_let
        vec
        logs
        landmarks
        fmt
        bisect_ppx
        qcheck
        alcotest
        qcheck-alcotest
        menhirLib
      ];

      checkInputs = [
        graph-easy
      ];
    }
