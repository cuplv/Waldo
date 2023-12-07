FSTAR_FILES := $(wildcard *.fsti) $(wildcard *.fst) $(wildcard */*.fsti) $(wildcard */*.fst)
INCLUDE_PATHS := effects
OTHERFLAGS += --record_hints --use_hints

.PHONY: all
all: verify
	@$(MAKE) -C examples/OTP

.PHONY: clean depend
include Makefile.common

CHECKED_FILES = $(addprefix $(CACHE_DIR)/,$(addsuffix .checked, $(notdir $(FSTAR_FILES))))

.PHONY: verify
verify: $(CHECKED_FILES)

.PHONY: clean-hints
clean: clean-hints
clean-hints:
	$(RM) $(wildcard *.hints)
