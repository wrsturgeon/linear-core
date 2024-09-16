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
_CoqProject
.direnv
.filestoinstall
.gitignore
$(MCOQ)
$(MCOQ).conf
$(OCAMLDIR)
out*
result
*.aux
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
ocaml/build:

%: $(COQMK) .gitignore
	+$(MAKE) $(MAKE_FLAGS) -f $< $@

$(COQMK):
	if [ -f $@ ]; then :; else echo '`$(COQMK)` missing!'; exit 1; fi

.gitignore: Makefile
	echo -e $(call escape_str,$(GIT_IGNORE)) > $@

Makefile:
	if [ -f $@ ]; then :; else echo '`Makefile` missing!'; exit 1; fi
