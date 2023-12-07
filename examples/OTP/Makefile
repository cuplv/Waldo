# Since this file is located in Waldo/examples/OTP, the Waldo directory is 2 levels up.
WALDO_DIR := ../..

INCLUDE_PATHS := $(WALDO_DIR) $(WALDO_DIR)/effects
FSTAR_FILES := $(wildcard *.fsti) $(wildcard *.fst)
CACHE_DIR := $(WALDO_DIR)/_cache
OTHERFLAGS += --record_hints --use_hints

.PHONY: all
all: verify

.PHONY: clean depend
include ../../Makefile.common

CHECKED_FILES = $(addprefix $(CACHE_DIR)/,$(addsuffix .checked, $(notdir $(FSTAR_FILES))))

.PHONY: verify
verify: $(CHECKED_FILES)

.PHONY: clean-hints
clean: clean-hints
clean-hints:
	$(RM) $(wildcard *.hints)
