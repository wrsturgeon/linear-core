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
          dune = versions.dune or ocaml-pkgs.dune_3;
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
            installPhase =
              let
                coq-install-path = "lib/coq/${context.coq.coq-version}/user-contrib";
              in
              ''
                mkdir -p ''${out}/${coq-install-path}
                mv theories ''${out}/${coq-install-path}/${cname}

                mkdir -p ''${out}/${ocaml-src-install-path}
                mv ocaml ''${out}/${ocaml-src-install-path}/${uname}
              '';
          };
        with-context =
          context:
          let
            coq-built = self.lib.coq-with-context context;
            inherit (context.pkgs.lib) strings;
            escape = strings.escapeShellArg;
            dune-version-full = context.dune.version;
            dune-version-parts = strings.splitString "." dune-version-full;
            dune-version-2-part = context.pkgs.lib.lists.take 2 dune-version-parts;
            dune-version = strings.concatStringsSep "." dune-version-2-part;
            dune-project-contents = ''
              (lang dune ${dune-version})
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
            pname = uname;
            inherit version;
            src = "${coq-built}/${ocaml-src-install-path}/${uname}";
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
              context = self.lib.context-with-versions { inherit pkgs; };
            in
            with context;
            coq-pkgs.mkCoqDerivation {
              inherit pname;
              version = "none";
              buildInputs = [ (self.lib.coq-with-context context) ];
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
              context = self.lib.context-with-versions { inherit pkgs; };
            in
            with context;
            ocaml-pkgs.buildDunePackage {
              inherit pname;
              version = "none";
              propagatedBuildInputs = [
                (builtins.trace "${self.lib.with-context context}" (self.lib.with-context context))
              ];
              src = pkgs.stdenvNoCC.mkDerivation {
                name = "${pname}-src";
                src = ./.;
                buildInputs = with context; [ dune ];
                buildPhase = ''
                  dune init proj ${pname} ./${pname}
                  sed -i '1s/^/open LinearCore\n/' ${pname}/bin/main.ml
                '';
                installPhase = "cp -Lr . $out";
              };
              buildPhase = ''
                ocamlfind list
                dune build
              '';
            };
        };
        devShells.default = self.lib.shell-with-versions { inherit pkgs; };
      }
    );
}
