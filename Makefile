COQC ?= coqc
COQDEP ?= coqdep

COQFLAGS := \
	-q \
	-w -deprecated-hint-without-locality \
	-w -deprecated-instance-without-locality \
	-w -notation-incompatible-prefix \
	-w -notation-overriden \
	-w -ambiguous-paths \
	-w -redundant-canonical-projection \
	-w -cannot-define-projection \
	-require-import ExtLib.Structures.Monad

SOURCES := Behavior.v Optimizations.v KVSortedList.v
OBJECTS := $(SOURCES:.v=.vo)

PRIME_EXAMPLES_DIR := prime-examples
IMP_SYSTEM_DIR := $(PRIME_EXAMPLES_DIR)/imp_system
PRIME_LOADPATH := \
	-exclude-dir imp_system \
	-Q $(PRIME_EXAMPLES_DIR) '' \
	-Q $(IMP_SYSTEM_DIR) CRIS.imp_system
PRIME_SOURCES := $(shell find $(PRIME_EXAMPLES_DIR) \
	-type f -name '*.v' | sort)
PRIME_OBJECTS := $(PRIME_SOURCES:.v=.vo)
PRIME_DEPS := .prime-deps.mk
PRIME_COQFLAGS := $(COQFLAGS) $(PRIME_LOADPATH)

ifneq ($(filter prime,$(MAKECMDGOALS)),)
-include $(PRIME_DEPS)
endif

.PHONY: all prime check clean

all: $(OBJECTS)

prime: $(PRIME_OBJECTS)

$(OBJECTS): %.vo: %.v Makefile
	@echo "COQC $<"
	@$(COQC) $(COQFLAGS) $<

$(PRIME_OBJECTS): %.vo: %.v Makefile
	@echo "COQC $<"
	@$(COQC) $(PRIME_COQFLAGS) $<

$(PRIME_DEPS): Makefile $(PRIME_SOURCES)
	@$(COQDEP) $(PRIME_LOADPATH) $(PRIME_SOURCES) > $@

check: all
	@if grep -nE '(^|[^[:alnum:]_])(Admitted|admit)([^[:alnum:]_]|$$)' \
		$(SOURCES); then \
		echo "Unexpected admitted proof in workshop Rocq files" >&2; \
		exit 1; \
	fi

clean:
	find . -maxdepth 1 -type f \
		\( -name '*.aux' -o -name '*.glob' -o -name '*.vo' \
		-o -name '*.vok' -o -name '*.vos' -o -name '*.cache' \) \
		-delete
	find $(PRIME_EXAMPLES_DIR) -type f \
		\( -name '*.aux' -o -name '*.glob' -o -name '*.vo' \
		-o -name '*.vok' -o -name '*.vos' -o -name '*.cache' \) \
		-delete
	rm -f .lia.cache .nia.cache $(PRIME_DEPS)
