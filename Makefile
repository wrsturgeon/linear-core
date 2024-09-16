COMMON_MAKE_FLAGS:=--no-builtin-rules --no-builtin-variables

ifndef VERBOSE
.SILENT:
export MAKE_FLAGS:=$(COMMON_MAKE_FLAGS) --silent
else
export MAKE_FLAGS:=$(COMMON_MAKE_FLAGS) --no-silent --warn-undefined-variables
endif

export UPPERNAME:=LinearCore
export LOWERNAME:=linear-core
export UNDERNAME:=$(subst -,_,$(LOWERNAME))

export MCOQ:=Makefile.coq
export COQMK:=coq.mk
export OCAMLMK:=ocaml.mk
export OCAMLDIR:=ocaml

define GIT_IGNORE
.direnv
.filestoinstall
.gitignore
$(MCOQ)
$(OCAMLDIR)
out*
result
*.aux
*.conf
*.d
*.glob
*.swp
*.vo*
endef
export GIT_IGNORE

define NEWLINE


endef
export NEWLINE

define escape_str
'$(subst ',\',$(subst $(NEWLINE),\n,$(1)))'
endef

# Main target:
build:

install:
	echo "Unfortunately, there's no standard way to install both Coq and OCaml libraries."
	echo "The former has no package manager, and the latter has multiple competing ones."
	echo "If you'd like to install this package so you can use it in your own projects,"
	echo "please look into Nix, the language-agnostic universal package manager,"
	echo "which has been a permanent solution to package management headaches for many,"
	echo "including yours truly. (All hail, amen, and so on--but do what you like.)"
	exit 1

%: $(COQMK) .gitignore
	+$(MAKE) $(MAKE_FLAGS) -f $< $@

$(COQMK):
	if [ -f $@ ]; then :; else echo '`$(COQMK)` missing!'; exit 1; fi

.gitignore: $(THIS_MAKEFILE)
	echo -e $(call escape_str,$(GIT_IGNORE)) > $@

$(THIS_MAKEFILE):
	if [ -f $@ ]; then :; else echo '`$(THIS_MAKEFILE)` missing!'; exit 1; fi
