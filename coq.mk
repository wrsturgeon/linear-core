# Updated with some ideas from <https://github.com/coq-community/manifesto/wiki/Project-build-scripts>

.PHONY: clean

export UPPERNAME:=LinearCore
export LOWERNAME:=linear-core
export UNDERNAME:=$(subst -,_,$(LOWERNAME))

MCOQ:=Makefile.coq
COQMK:=coq.mk
OCAMLMK:=ocaml.mk
OCAMLDIR:=ocaml
SRCDIR:=theories
SOURCES:=$(shell find $(SRCDIR) -name '*.v')

define GIT_IGNORE
_CoqProject
.direnv
.filestoinstall
.gitignore
.$(MCOQ).d
$(MCOQ)
$(MCOQ).conf
$(OCAMLDIR)
result
*.aux
*.glob
*.vo*
endef

define NEWLINE


endef
export NEWLINE

define ESCAPE
'$(subst ',\',$(subst $(NEWLINE),\n,$(1)))'
endef
export ESCAPE

$(OCAMLDIR)/some-bullshit:

$(OCAMLDIR)/%: $(OCAMLDIR) | $(OCAMLMK)
	$(MAKE) $(MAKE_FLAGS) -f ../$(OCAMLMK) -C $<

# Note that, although this target "really"
# compiles and verifies the whole Coq source,
# all that we care about in the long term is that
# it creates the OCaml source directory as a byproduct:
$(OCAMLDIR): $(MCOQ)
	$(MAKE) $(MAKE_FLAGS) -f $< # theories/Extract.vo # $@

clean: $(MCOQ)
	$(MAKE) $(MAKE_FLAGS) -f $< cleanall
	rm -fr $(shell echo '$(GIT_IGNORE)' | tr '\n' ' ')
	find . -name '*.aux' -o -name '*.glob' -o -name '*.ml' -o -name '*.mli' -o -name '*.swp' -o -name '*.vo' -o -name '*.vok' -o -name '*.vos' | xargs -r rm
	direnv allow

$(MCOQ): _CoqProject
	$(COQBIN)coq_makefile -f $< -o $@ $(SOURCES)

_CoqProject: $(SRCDIR) .gitignore
	echo '-Q $(SRCDIR) $(UPPERNAME)' > $@

.gitignore: Makefile $(COQMK)
	echo -e $(call ESCAPE,$(GIT_IGNORE)) > $@
