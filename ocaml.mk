.PHONY: clean
.SHELL: bash

DUNE_VERSION_FULL:=$(shell dune --version)
DUNE_VERSION:=$(shell echo '$(DUNE_VERSION_FULL)' | cut -d '.' -f -2)

define DUNE_PROJECT_CONTENTS
(lang dune $(DUNE_VERSION))
(name $(UNDERNAME))
(generate_opam_files true)
(source (github wrsturgeon/$(LOWERNAME)))
(authors "Will Sturgeon")
(maintainers "Will Sturgeon")
; (license LICENSE) ; TODO
(documentation https://github.com/wrsturgeon/$(LOWERNAME))
(package
	(name $(UNDERNAME))
	(synopsis "Core semantics for a linear functional programming language")
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

some-bullshit: dune-project dune lib/dune
	dune build --profile release

dune-project:
	echo -e $(call ESCAPE,$(DUNE_PROJECT_CONTENTS)) > $@

dune:
	echo -e $(call ESCAPE,$(DUNE_CONTENTS)) > $@

lib/dune:
	echo -e $(call ESCAPE,$(LIB_DUNE_CONTENTS)) > $@
