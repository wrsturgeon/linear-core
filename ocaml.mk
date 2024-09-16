.PHONY: build clean
.SHELL: bash

DUNE_VERSION_FULL:=$(shell dune --version)
DUNE_VERSION:=$(shell echo '$(DUNE_VERSION_FULL)' | cut -d '.' -f -2)
OCAML_VERSION:=$(shell ocamlc --version)

LIB_INSTALL_DIR:=$${out}/lib/ocaml/$(OCAML_VERSION)/site-lib

GITHUB_ACCOUNT=wrsturgeon
SYNOPSIS:=Core semantics for a linear functional programming language.

define DUNE_PROJECT_CONTENTS
(lang dune $(DUNE_VERSION))
(name $(UNDERNAME))
(generate_opam_files true)
(source (github $(GITHUB_ACCOUNT)/$(LOWERNAME)))
(authors "Will Sturgeon")
(maintainers "Will Sturgeon")
; (license LICENSE) ; TODO
(documentation https://github.com/$(GITHUB_ACCOUNT)/$(LOWERNAME))
(package
	(name $(UNDERNAME))
	(synopsis "$(SYNOPSIS)")
	; (description "TODO")
	(depends ocaml dune)
	; (tags (topics "to describe" your project))
)
endef

define DUNE_CONTENTS
(env
  (dev
    (flags
      (:standard -warn-error -A)
    )
  )
)
endef

define LIB_DUNE_CONTENTS
(library
  (name $(UNDERNAME))
	(public_name $(UNDERNAME))
)
endef

define escape_str
'$(subst ',\',$(subst $(NEWLINE),\n,$(1)))'
endef

build: _build/install/default/lib/$(UNDERNAME)

install: $(LIB_INSTALL_DIR)/$(UNDERNAME)

$(LIB_INSTALL_DIR)/$(UNDERNAME): _build/install/default/lib/$(UNDERNAME) $(LIB_INSTALL_DIR)
	cp -r $< $(LIB_INSTALL_DIR)/$(UNDERNAME)

$(LIB_INSTALL_DIR):
	mkdir -p $@

_build/install/default/lib/$(UNDERNAME): dune-project dune lib/dune
	dune build --profile release

dune-project:
	echo -e $(call escape_str,$(DUNE_PROJECT_CONTENTS)) > $@
	-if command -v gh &> /dev/null; then if [ "$$(gh api user --jq '.login')" = "$(GITHUB_ACCOUNT)" ]; then gh repo edit --description=$(call escape_str,$(SYNOPSIS)); fi; fi

dune:
	echo -e $(call escape_str,$(DUNE_CONTENTS)) > $@

lib/dune:
	echo -e $(call escape_str,$(LIB_DUNE_CONTENTS)) > $@
