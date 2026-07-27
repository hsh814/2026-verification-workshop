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

DAY1_DIR := day1
DAY1_LECTURE_SOURCES := \
	$(DAY1_DIR)/lectures/Behavior.v \
	$(DAY1_DIR)/lectures/ModuleIntro.v \
	$(DAY1_DIR)/lectures/RefinementIntro.v
DAY1_EXERCISE_SOURCES := \
	$(DAY1_DIR)/exercises/Optimizations.v \
	$(DAY1_DIR)/exercises/KVSortedList.v
DAY1_ANSWER_SOURCES := \
	$(DAY1_DIR)/answers/Optimizations.v \
	$(DAY1_DIR)/answers/KVSortedList.v
DAY1_COMPLETE_SOURCES := $(DAY1_LECTURE_SOURCES) $(DAY1_ANSWER_SOURCES)
SOURCES := \
	$(DAY1_LECTURE_SOURCES) \
	$(DAY1_EXERCISE_SOURCES) \
	$(DAY1_ANSWER_SOURCES)
OBJECTS := $(SOURCES:.v=.vo)
DAY1_LOADPATH := -Q $(DAY1_DIR) ''
DAY1_COQFLAGS := $(COQFLAGS) $(DAY1_LOADPATH)

PRIME_EXAMPLES_DIR := day3
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

SL_EXAMPLES_DIR := day2
SL_LOADPATH := \
	-Q $(SL_EXAMPLES_DIR) '' \
	-Q $(IMP_SYSTEM_DIR) CRIS.imp_system
SL_SOURCES := $(shell find $(SL_EXAMPLES_DIR) \
	-type f -name '*.v' | sort)
SL_OBJECTS := $(SL_SOURCES:.v=.vo)
SL_ANSWER_SOURCES := $(shell find $(SL_EXAMPLES_DIR) \
	-type f -path '*_answer/*.v' | sort)
SL_DEPS := .sl-deps.mk
SL_COQFLAGS := $(COQFLAGS) $(SL_LOADPATH)

ifneq ($(filter prime sl day2 day3 day2/% day3/%,$(MAKECMDGOALS)),)
-include $(PRIME_DEPS)
endif

ifneq ($(filter sl day2 day2/%,$(MAKECMDGOALS)),)
-include $(SL_DEPS)
endif

.PHONY: all day1 day2 day3 prime sl check \
	check-day1-exercises check-day1-answers check-sl-answers clean

all: day1

day1: $(OBJECTS)

day2: $(SL_OBJECTS) check-sl-answers

day3: $(PRIME_OBJECTS)

prime: day3

sl: day2

check-day1-exercises:
	@if grep -nE '^[[:space:]]*(Abort|admit)[[:space:].]' \
		$(DAY1_EXERCISE_SOURCES); then \
		echo "Unexpected unfinished proof form in Day 1 exercises" >&2; \
		exit 1; \
	fi
	@count=$$(grep -hE '^[[:space:]]*Admitted[[:space:]]*\.' \
		$(DAY1_EXERCISE_SOURCES) | wc -l); \
	if [ "$$count" -ne 6 ]; then \
		echo "Expected 6 admitted Day 1 exercises, found $$count" >&2; \
		exit 1; \
	fi

check-day1-answers:
	@if grep -nE '^[[:space:]]*(Abort|Admitted|admit)[[:space:].]' \
		$(DAY1_COMPLETE_SOURCES); then \
		echo "Unexpected unfinished proof in Day 1 lecture or answer files" >&2; \
		exit 1; \
	fi

check-sl-answers:
	@if grep -nE '(^|[^[:alnum:]_])(Admitted|admit)([^[:alnum:]_]|$$)' \
		$(SL_ANSWER_SOURCES); then \
		echo "Unexpected admitted proof in separation-logic answers" >&2; \
		exit 1; \
	fi

$(OBJECTS): %.vo: %.v Makefile
	@echo "COQC $<"
	@$(COQC) $(DAY1_COQFLAGS) $<

$(PRIME_OBJECTS): %.vo: %.v Makefile
	@echo "COQC $<"
	@$(COQC) $(PRIME_COQFLAGS) $<

$(PRIME_DEPS): Makefile $(PRIME_SOURCES)
	@$(COQDEP) $(PRIME_LOADPATH) $(PRIME_SOURCES) > $@

$(SL_OBJECTS): %.vo: %.v Makefile
	@echo "COQC $<"
	@$(COQC) $(SL_COQFLAGS) $<

$(SL_DEPS): Makefile $(SL_SOURCES)
	@$(COQDEP) $(SL_LOADPATH) $(SL_SOURCES) > $@

check: day1 check-day1-exercises check-day1-answers

clean:
	find $(DAY1_DIR) $(SL_EXAMPLES_DIR) $(PRIME_EXAMPLES_DIR) -type f \
		\( -name '*.aux' -o -name '*.glob' -o -name '*.vo' \
		-o -name '*.vok' -o -name '*.vos' -o -name '*.cache' \) \
		-delete
	rm -f .lia.cache .nia.cache $(PRIME_DEPS) $(SL_DEPS)
