# Updated with some ideas from <https://github.com/coq-community/manifesto/wiki/Project-build-scripts>

.PHONY: build clean
SHELL:=bash

SRCDIR:=theories

define escape_str
'$(subst ',\',$(subst $(NEWLINE),\n,$(1)))'
endef

build-coq: $(OCAMLDIR)

# This target compiles and verifies the whole Coq source,
# but all we care about in the long term is that it
# creates the OCaml source directory as a byproduct:
$(OCAMLDIR): $(MCOQ)
	+$(MAKE) $(MAKE_FLAGS) -f $< # theories/Extract.vo # $@

build: $(OCAMLDIR)/build

$(OCAMLDIR)/%: $(OCAMLDIR) $(OCAMLMK)
	+$(MAKE) $(MAKE_FLAGS) -C $< -f ../$(OCAMLMK) $*

clean: $(MCOQ)
	+$(MAKE) $(MAKE_FLAGS) -f $< cleanall
	rm -fr $(subst $(NEWLINE), ,$(GIT_IGNORE))
	find . -name '*.aux' -o -name '*.d' -o -name '*.glob' -o -name '*.ml' -o -name '*.mli' -o -name '*.swp' -o -name '*.vo' -o -name '*.vok' -o -name '*.vos' | xargs -r rm
	+$(MAKE) .gitignore
	direnv allow

$(MCOQ): $(THIS_MAKEFILE) $(COQMK)
	coq_makefile -Q $(SRCDIR) $(UPPERNAME) -o $@ $(shell find $(SRCDIR) -name '*.v')
