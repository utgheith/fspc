
FSTAR       ?= fstar.exe
CACHE       ?= _cache
FSTAR_FLAGS ?=

# 241: "no checked file yet, will check": the cache being filled.
# 321: the standard library's checked files live with F*, not in $(CACHE).
FLAGS := --cache_checked_modules --cache_dir $(CACHE) --warn_error -241-321 $(FSTAR_FLAGS)

SRCS    := $(sort $(wildcard *.fst *.fsti))
MODULES := $(sort $(basename $(SRCS)))
CHECKED := $(SRCS:%=$(CACHE)/%.checked)

.PHONY: all clean $(MODULES)
.NOTPARALLEL:

all: $(CHECKED)

$(MODULES): %: $(CACHE)/%.fst.checked

$(CACHE)/%.checked:
	@echo "== $<"
	@$(FSTAR) $(FLAGS) $<
	@touch -c $@

$(CACHE)/.depend: $(SRCS)
	@mkdir -p $(CACHE)
	@$(FSTAR) $(FLAGS) --dep full $(SRCS) --output_deps_to $@.all
	@awk 'BEGIN { RS = ""; ORS = "\n\n" } $$1 !~ /^\// { print }' $@.all > $@
	@rm -f $@.all

ifneq ($(MAKECMDGOALS),clean)
include $(CACHE)/.depend
endif

clean:
	rm -rf $(CACHE)
