{
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    mmaps-src = {
      flake = false;
      url = "github:coq-community/coq-mmaps";
    };
    nix-filter.url = "github:numtide/nix-filter";
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
  };
  outputs =
    {
      flake-utils,
      mmaps-src,
      nix-filter,
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
        src = nix-filter {
          root = ./.;
          include = [
            "Makefile"
            "coq.mk"
            "theories"
          ];
        };
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
            inherit version;
            inherit (self.lib) src;
            pname = "${pname}-coq";
            propagatedBuildInputs = (with context; [ mmaps ]) ++ (with context.coq-pkgs; [ equations ]);
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
        checker =
          overrides:
          pkgs.stdenvNoCC.mkDerivation (
            {
              inherit (self.lib) src;
              name = "check";
              buildPhase = ":";
              installPhase = "mkdir -p $out";
              buildInputs = [ ];
            }
            // overrides
          );
        example =
          script:
          pkgs.stdenvNoCC.mkDerivation {
            inherit (self.lib) src;
            name = "example";
            buildPhase = ":";
            installPhase =
              let
                with-shabang = ''
                  #!${pkgs.bash}/bin/bash
                  set -eu
                  ${script}
                '';
              in
              ''
                mkdir -p $out/bin
                echo ${pkgs.lib.strings.escapeShellArg with-shabang} > $out/bin/example
                chmod +x $out/bin/example
              '';
          };
        rg = "${pkgs.ripgrep}/bin/rg";
      in
      {
        packages = {
          context = self.lib.context-with-versions { inherit pkgs; };
          coq-only = self.lib.coq-with-versions { inherit pkgs; };
          default = self.lib.with-versions { inherit pkgs; };
          example-interpreter =
            with self.packages.${system}.context;
            ocaml-pkgs.buildDunePackage {
              pname = "example_interpreter";
              version = "none";
              src = self.packages.${system}.example-interpreter-src;
              propagatedBuildInputs = [ (self.lib.with-context self.packages.${system}.context) ];
            };
          example-interpreter-src =
            let
              main-ml = ''
                open Linear_core

                let rec interpret context t =
                  let stepped = Linear_core.SmallStepFunction.step context t in
                  let formatted = Linear_core.SmallStepFunction.to_string stepped in
                  print_endline formatted;
                  match stepped with None -> None | Some (context', t') -> interpret context' t'

                let _ =
                  let err = Linear_core.Term.Ctr (Linear_core.Constructor.Builtin Linear_core.Constructor.Error) in
                  let mov = (fun x -> Linear_core.Term.Var (x, Linear_core.Ownership.Owned)) in
                  let term =
                    Linear_core.Term.App (
                      Linear_core.Term.Cas (
                        Linear_core.Pattern.Nam "x",
                        mov "x",
                        Linear_core.Term.Cas (
                          Linear_core.Pattern.Nam "x",
                          mov "x",
                          mov "x")),
                      Linear_core.Term.App (
                        Linear_core.Term.Cas (
                          Linear_core.Pattern.Nam "x",
                          err,
                          err),
                        err)) in
                  let stringified = Linear_core.Term.to_string term in
                  print_endline "Original term:";
                  print_endline stringified;
                  print_endline "";
                  interpret Linear_core.Map.empty term
              '';
              uname = "example_interpreter";
            in
            pkgs.stdenvNoCC.mkDerivation {
              name = "example-interpreter-src";
              src = nix-filter {
                root = ./.;
                include = [ ];
              };
              buildInputs = with self.packages.${system}.context; [ dune ];
              buildPhase = ''
                dune init proj ${uname} ./${uname}
                sed -i 's/libraries/libraries linear_core/g' ${uname}/bin/dune
                echo ${pkgs.lib.strings.escapeShellArg main-ml} > ${uname}/bin/main.ml
              '';
              installPhase = "cp -Lr ./${uname} $out";
            };
          example-unshadow =
            with self.packages.${system}.context;
            ocaml-pkgs.buildDunePackage {
              pname = "example_unshadow";
              version = "none";
              src = self.packages.${system}.example-unshadow-src;
              propagatedBuildInputs = [ (self.lib.with-context self.packages.${system}.context) ];
            };
          example-unshadow-src =
            let
              main-ml = ''
                open Linear_core

                let () =
                  let err = Linear_core.Term.Ctr (Linear_core.Constructor.Builtin Linear_core.Constructor.Error) in
                  let mov = (fun x -> Linear_core.Term.Var (x, Linear_core.Ownership.Owned)) in
                  let term =
                    Linear_core.Term.App (
                      Linear_core.Term.Cas (
                        Linear_core.Pattern.Nam "x",
                        mov "x",
                        Linear_core.Term.Cas (
                          Linear_core.Pattern.Nam "x",
                          mov "x",
                          mov "x")),
                      Linear_core.Term.App (
                        Linear_core.Term.Cas (
                          Linear_core.Pattern.Nam "x",
                          err,
                          err),
                        err)) in
                  let stringified = Linear_core.Term.to_string term in
                  print_endline "Original term:";
                  print_endline stringified;
                  print_endline "";
                  match Linear_core.Unshadow.unshadow term with
                  | None ->
                      print_endline "ERROR: FAILED TO UNSHADOW";
                      exit 1
                  | Some unshadowed ->
                      let stringified_unshadowed = Linear_core.Term.to_string unshadowed in
                      print_endline "Unshadowed:";
                      print_endline stringified_unshadowed
              '';
              uname = "example_unshadow";
            in
            pkgs.stdenvNoCC.mkDerivation {
              name = "example-unshadow-src";
              src = nix-filter {
                root = ./.;
                include = [ ];
              };
              buildInputs = with self.packages.${system}.context; [ dune ];
              buildPhase = ''
                dune init proj ${uname} ./${uname}
                sed -i 's/libraries/libraries linear_core/g' ${uname}/bin/dune
                echo ${pkgs.lib.strings.escapeShellArg main-ml} > ${uname}/bin/main.ml
              '';
              installPhase = "cp -Lr ./${uname} $out";
            };
          examples = example (
            pkgs.lib.strings.concatStrings (
              builtins.map
                (
                  name:
                  let
                    bin = "${self.packages.${system}.${name}}/bin";
                    cut = "${pkgs.coreutils}/bin/cut";
                    echo = "${pkgs.coreutils}/bin/echo";
                    rev = "${pkgs.util-linux}/bin/rev";
                  in
                  ''

                    if [ -d ${bin} ]; then
                      for run in ${bin}/*; do
                        if [ -x ''${run} ]; then
                          ${echo}
                          ${echo} '%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Running `${pkgs.lib.removePrefix "example-" name}` (binary `'"$(${echo} "''${run}" | ${rev} | ${cut} -d '/' -f 1 | ${rev})"'`)...'
                          ${echo}
                          ''${run}
                        fi
                      done
                    fi
                  ''
                )
                (
                  builtins.filter (pkgs.lib.strings.hasPrefix "example-") (builtins.attrNames self.packages.${system})
                )
            )
          );
          test-syntax = checker {
            buildPhase = ''
              # if ${rg} 'Admitted|Axiom|Conjecture|Parameter|Hypothesis|Hypotheses|Variable' -g '*.v'; then
              if ${rg} 'Admitted|Axiom|Conjecture|Parameter|Hypothesis|Hypotheses|Variable' -g '*.v' -g '!theories/NewNames.v'; then
                echo
                echo 'SYNTAX ERROR: unverified assumption (above)'
                exit 1
              fi

              if ${rg} ' $'; then
                echo
                echo 'SYNTAX ERROR: trailing whitespace (above)'
                exit 1
              fi

              if ${rg} ':$' -g '*.v'; then
                echo
                echo 'SYNTAX ERROR: colons before types should begin their own lines (above)'
                exit 1
              fi

            '';
          };
          test-coq =
            with self.packages.${system}.context;
            coq-pkgs.mkCoqDerivation {
              pname = "test-coq";
              version = "none";
              buildInputs = [ (self.lib.coq-with-context self.packages.${system}.context) ];
              src = self.packages.${system}.test-coq-src;
              buildPhase = ''
                coq_makefile -o Makefile $(find . -name '*.v')
                make
              '';
            };
          test-coq-src = pkgs.writeTextFile {
            name = "test-coq-src";
            destination = "/theories/Test.v";
            text = ''
              From ${cname} Require Map.
            '';
          };
          test-ocaml =
            with self.packages.${system}.context;
            ocaml-pkgs.buildDunePackage {
              pname = "test_ocaml";
              version = "none";
              src = self.packages.${system}.test-ocaml-src;
              propagatedBuildInputs = [
                (self.lib.with-context self.packages.${system}.context)
              ];
            };
          test-ocaml-src =
            let
              pname = "test_ocaml";
            in
            pkgs.stdenvNoCC.mkDerivation {
              name = "test-ocaml-src";
              src = nix-filter {
                root = ./.;
                include = [ ];
              };
              buildInputs = with self.packages.${system}.context; [ dune ];
              buildPhase = ''
                dune init proj ${pname} ./${pname}
                sed -i 's/libraries/libraries linear_core/g' ${pname}/bin/dune
                sed -i '1s/^/open Linear_core\n/' ${pname}/bin/main.ml
              '';
              installPhase = "cp -Lr ./${pname} $out";
            };
          tests = checker {
            buildInputs = builtins.map (pkg: self.packages.${system}.${pkg}) (
              builtins.filter (pkgs.lib.strings.hasPrefix "test-") (builtins.attrNames self.packages.${system})
            );
          };
        };
        devShells.default = self.lib.shell-with-versions { inherit pkgs; };
      }
    );
}
