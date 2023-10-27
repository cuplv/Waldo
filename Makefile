FSTAR ?= fstar.exe
Z3 ?= z3

INC_DIRS ?= "effects"
INC_FLAGS := $(addprefix --include , $(INC_DIRS))

FSTAR_FLAGS := $(INC_FLAGS) \
			   --smt $(Z3) \
			   --use_hints

SPECS := $(wildcard *.fsti) $(wildcard *.fst) $(wildcard */*.fsti) $(wildcard */*.fst)

.PHONY: all
all: help verify
	@$(MAKE) -C examples/OTP

.PHONY: help
help:
	@echo "This Makefile checks all .fst and .fsti specifications in the current and child directories.\n"

.PHONY: verify
verify: $(SPECS)
	for spec in $(SPECS); do \
		$(FSTAR) $$spec $(FSTAR_FLAGS) ; \
	done

.PHONY: gen_hints
gen_hints: $(SPECS)
	for spec in $(SPECS); do \
		$(FSTAR) $$spec $(FSTAR_FLAGS) --record_hints ; \
	done

.PHONY: clean
clean:
	rm $(wildcard *.hints)
