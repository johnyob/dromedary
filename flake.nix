{
  description = "Dromedary Nix Flake";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    treefmt = {
      url = "github:numtide/treefmt-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    # OCaml overlay
    ocaml-overlay = {
      url = "github:nix-ocaml/nix-overlays";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = inputs:
    with inputs;
      flake-utils.lib.eachDefaultSystem (system: let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [
            ocaml-overlay.overlays.default
            (import ./nix/overlay.nix)
          ];
        };

        fmt = treefmt.lib.evalModule pkgs {
          projectRootFile = "flake.nix";

          programs.alejandra.enable = true;
          programs.ocamlformat = {
            enable = true;
            package = pkgs.ocamlformat_0_26_2;
          };

          settings.global.excludes = ["result" ".direnv" "_build" "_coverage"];
        };

        dromedary = pkgs.callPackage ./. {};
      in {
        packages.default = dromedary;

        formatter = fmt.config.build.wrapper;

        devShells.default = pkgs.mkShell {
          name = "dromedary-dev-shell";

          inputsFrom = [dromedary];

          buildInputs = with pkgs; [
            # Formatters
            alejandra
            shellcheck
            ocamlformat_0_26_2

            # OCaml devenv
            ocamlPackages.utop
            ocamlPackages.ocaml-lsp
            ocamlPackages.merlin
            ocamlPackages.merlin-lib

            # Test dependencies
            graph-easy
          ];
        };
      });
}
