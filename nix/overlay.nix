final: prev:
with prev; {
  ocamlPackages = final.ocaml-ng.ocamlPackages_5_2;
  ocamlformat = final.ocamlPackages.ocamlformat_0_21_0;

  ocaml-ng =
    ocaml-ng
    // (with ocaml-ng; {
      ocamlPackages_5_2 = ocamlPackages_5_2.overrideScope (_: prev:
        with prev; {
          vec = buildDunePackage rec {
            pname = "vec";
            version = "0.3.0";
            src = fetchurl {
              url = "https://github.com/aionescu/vec/archive/refs/tags/v${version}.tar.gz";
              hash = "sha256-I5OvoGjH6UkI4c5F5B9bmNImKzzjZWai9D9BkE4ZsqI=";
            };

            minimumOCamlVersion = "4.08";
          };
        });
    });
}
