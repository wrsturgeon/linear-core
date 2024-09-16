{
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    mmaps-src = {
      flake = false;
      url = "github:coq-community/coq-mmaps";
    };
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
  };
  outputs =
    {
      flake-utils,
      mmaps-src,
      nixpkgs,
      self,
    }:
    let
      pname = "linear-core";
      version = "0.0.1";
      src = ./.;
    in
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system; };
        coq-pkgs = pkgs.coqPackages;
        inherit (coq-pkgs) coq;
        ocaml-pkgs = coq.ocamlPackages;
        mmaps = coq-pkgs.mkCoqDerivation {
          pname = "mmaps";
          version = "main";
          src = mmaps-src;
        };
        propagatedBuildInputs = [ mmaps ];
        buildInputs = with ocaml-pkgs; [
          dune_3
          ocaml
        ];
      in
      {
        packages.default = coq-pkgs.mkCoqDerivation {
          inherit
            pname
            version
            src
            propagatedBuildInputs
            buildInputs
            ;
        };
        devShells.default = pkgs.mkShell {
          inputsFrom = [ self.packages.${system}.default ];
          packages = (with ocaml-pkgs; [ ocamlformat ]) ++ (with pkgs; [ gh ]);
        };
      }
    );
}
