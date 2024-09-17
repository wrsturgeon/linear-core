# Updated with some ideas from <https://github.com/coq-community/manifesto/wiki/Project-build-scripts>

.PHONY: build clean
SHELL:=bash

SRCDIR:=theories
SOURCES:=$(shell find $(SRCDIR) -name '*.v')

define escape_str
'$(subst ',\',$(subst $(NEWLINE),\n,$(1)))'
endef

build: ocaml

# This target compiles and verifies the whole Coq source,
# so why name it `ocaml`?
# All we care about in the long term is that it
# creates the OCaml source directory as a byproduct.
ocaml: $(MCOQ)
	+$(MAKE) $(MAKE_FLAGS) -f $<

clean: $(MCOQ)
	+$(MAKE) $(MAKE_FLAGS) -f $< cleanall
	rm -fr $(subst $(NEWLINE), ,$(GIT_IGNORE))
	find . -name '*.aux' -o -name '*.conf' -o -name '*.d' -o -name '*.glob' -o -name '*.ml' -o -name '*.mli' -o -name '*.swp' -o -name '*.vo' -o -name '*.vok' -o -name '*.vos' | xargs -r rm
	+$(MAKE) .gitignore
	direnv allow

$(MCOQ): _CoqProject $(SOURCES)
	coq_makefile -f $< -o $@ $(SOURCES)

_CoqProject: $(THIS_MAKEFILE) $(COQMK)
	echo '-Q $(SRCDIR) $(UPPERNAME)' > $@
