COMMON_MAKE_FLAGS:=--no-builtin-rules --no-builtin-variables

ifndef VERBOSE
.SILENT:
export MAKE_FLAGS:=$(COMMON_MAKE_FLAGS) --silent
else
export MAKE_FLAGS:=$(COMMON_MAKE_FLAGS)
endif

ocaml/some-bullshit:

%: coq.mk
	$(MAKE) $(MAKE_FLAGS) -f $< $@

coq.mk:
	if [ -f $@ ]; then :; else echo '`coq.mk` missing!'; exit 1; fi
