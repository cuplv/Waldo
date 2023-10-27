FSTAR ?= fstar.exe
Z3 ?= z3

# Since this file is located in Waldo/examples/OTP, the Waldo directory is 2 levels up.
WALDO_DIR := ../../

INC_DIRS ?= "$(WALDO_DIR)" \
			"$(WALDO_DIR)/effects"
INC_FLAGS := $(addprefix --include , $(INC_DIRS))

FSTAR_FLAGS := $(INC_FLAGS) \
			   --smt $(Z3) \
			   --use_hints

SPECS := $(wildcard *.fsti) $(wildcard *.fst)

.PHONY: all
all: help verify

.PHONY: help
help:
	@echo "This Makefile checks all .fst and .fsti specifications in the current directory.\n"

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
