# Updated with some ideas from <https://github.com/coq-community/manifesto/wiki/Project-build-scripts>

.PHONY: build clean

SRCDIR:=theories
SOURCES:=$(shell find $(SRCDIR) -name '*.v')

COQ_VERSION:=$(coqc --print-version | cut -d '.' -f -2)
INSTALL_DIR:=$${out}/lib/coq/$(COQ_VERSION)/user-contrib

define escape_str
'$(subst ',\',$(subst $(NEWLINE),\n,$(1)))'
endef

build: $(OCAMLDIR)/build

install: $(INSTALL_DIR)/$(UPPERNAME)

$(INSTALL_DIR)/$(UPPERNAME): theories $(INSTALL_DIR) $(OCAMLDIR)/install
	cp -r $< $(INSTALL_DIR)/$(UPPERNAME)

$(INSTALL_DIR):
	mkdir -p $@

$(OCAMLDIR)/%: $(OCAMLDIR) $(OCAMLMK)
	+$(MAKE) $(MAKE_FLAGS) -C $< -f ../$(OCAMLMK) $*

# Note that, although this target "really"
# compiles and verifies the whole Coq source,
# all that we care about in the long term is that
# it creates the OCaml source directory as a byproduct:
$(OCAMLDIR): $(MCOQ)
	+$(MAKE) $(MAKE_FLAGS) -f $< # theories/Extract.vo # $@

clean: $(MCOQ)
	+$(MAKE) $(MAKE_FLAGS) -f $< cleanall
	rm -fr $(subst $(NEWLINE), ,$(GIT_IGNORE))
	find . -name '*.aux' -o -name '*.d' -o -name '*.glob' -o -name '*.ml' -o -name '*.mli' -o -name '*.swp' -o -name '*.vo' -o -name '*.vok' -o -name '*.vos' | xargs -r rm
	+$(MAKE) .gitignore
	direnv allow

$(MCOQ): _CoqProject
	$(COQBIN)coq_makefile -f $< -o $@ $(SOURCES)

_CoqProject: Makefile
	echo '-Q $(SRCDIR) $(UPPERNAME)' > $@
