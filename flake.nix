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
      uname = "linear_core";
      cname = "LinearCore";
      version = "0.0.1";
      synopsis = "Core semantics for a linear functional programming language.";
      ocaml-src-install-path = "lib/ocaml";
    in
    {
      lib = {
        context-with-versions = versions: rec {
          inherit (versions) pkgs;
          coq-pkgs = versions.coq-pkgs or pkgs.coqPackages;
          coq = versions.coq or coq-pkgs.coq;
          ocaml-pkgs = versions.ocaml-pkgs or coq.ocamlPackages;
          mmaps = versions.mmaps or coq-pkgs.mkCoqDerivation {
            pname = "mmaps";
            version = "main";
            src = mmaps-src;
          };
        };
        coq-with-context =
          context:
          context.coq-pkgs.mkCoqDerivation {
            pname = "${pname}-coq";
            inherit version;
            src = ./.;
            propagatedBuildInputs = with context; [ mmaps ];
            buildPhase = ''
              make build-coq
            '';
            installPhase =
              let
                coq-install-path = "lib/coq/${context.coq.coq-version}/user-contrib";
              in
              ''
                mkdir -p ''${out}/${coq-install-path}
                mv theories ''${out}/${coq-install-path}/${pname}

                mkdir -p ''${out}/${ocaml-src-install-path}
                mv ocaml ''${out}/${ocaml-src-install-path}/${pname}
              '';
          };
        with-context =
          context:
          let
            coq-built = self.lib.coq-with-context context;
            escape = context.pkgs.lib.strings.escapeShellArg;
            dune-project-contents = ''
              (lang dune ${context.dune.version})
              (name ${uname})
              (generate_opam_files true)
              (source (github wrsturgeon/${pname}))
              (authors "Will Sturgeon")
              (maintainers "Will Sturgeon")
              ; (license LICENSE) ; TODO
              (documentation https://github.com/wrsturgeon/${pname})
              (package
              	(name ${uname})
              	(synopsis "${synopsis}")
              	; (description "TODO")
              	(depends ocaml dune)
              	; (tags (topics "to describe" your project))
              )
            '';
            dune-contents = ''
              (env
                (dev
                  (flags
                    (:standard -warn-error -A)
                  )
                )
              )
            '';
            lib-dune-contents = ''
              (library
                (name ${uname})
              	(public_name ${uname})
              )
            '';
          in
          context.ocaml-pkgs.buildDunePackage {
            inherit pname version;
            src = "${coq-built}/${ocaml-src-install-path}/${pname}";
            propagatedBuildInputs = [ coq-built ];
            configurePhase = ''
              echo ${escape dune-project-contents} > dune-project
              echo ${escape dune-contents} > dune
              echo ${escape lib-dune-contents} > lib/dune
            '';
          };
        coq-with-versions = versions: self.lib.coq-with-context (self.lib.context-with-versions versions);
        with-versions = versions: self.lib.with-context (self.lib.context-with-versions versions);
        shell-with-context =
          context:
          context.pkgs.mkShell {
            inputsFrom = builtins.map (f: f context) (
              with self.lib;
              [
                coq-with-context
                with-context
              ]
            );
            packages =
              (with context.ocaml-pkgs; [
                ocamlformat
              ])
              ++ (with context.pkgs; [ gh ]);
          };
        shell-with-versions =
          versions: self.lib.shell-with-context (self.lib.context-with-versions versions);
      };
    }
    // flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system; };
        coq-pkgs = pkgs.coqPackages;
        ocaml-pkgs = coq-pkgs.coq.ocamlPackages;
      in
      {
        packages = {
          default = self.lib.with-versions { inherit pkgs; };
          coq-only = self.lib.coq-with-versions { inherit pkgs; };
          tests = pkgs.stdenvNoCC.mkDerivation {
            name = "tests";
            buildInputs = with self.packages.${system}; [
              test-coq
              test_ocaml
            ];
          };
          test-coq =
            let
              pname = "test-coq";
            in
            coq-pkgs.mkCoqDerivation {
              inherit pname;
              version = "none";
              buildInputs = [ (self.packages.${system}.coq-only) ];
              src = pkgs.writeTextFile {
                name = "${pname}-src";
                destination = "/theories/Test.v";
                text = ''
                  From LinearCore Require Map.
                '';
              };
              buildPhase = ''
                coq_makefile -o Makefile $(find . -name '*.v')
                make
              '';
            };
          test_ocaml =
            let
              pname = "test_ocaml";
            in
            ocaml-pkgs.buildDunePackage {
              inherit pname;
              version = "none";
              buildInputs = [ (self.packages.${system}.default) ];
              src = pkgs.stdenvNoCC.mkDerivation {
                name = "${pname}-src";
                src = ./.;
                buildInputs = with ocaml-pkgs; [ dune_3 ];
                buildPhase = ''
                  dune init proj ${pname} ${pname}
                  sed -i '1s/^/open LinearCore\n/' ${pname}/bin/main.ml
                '';
                installPhase = "cp -Lr . $out";
              };
            };
        };
        devShells.default = self.lib.shell-with-versions { inherit pkgs; };
      }
    );
}
