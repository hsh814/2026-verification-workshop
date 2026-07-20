CRIS_DIR ?= ../CRIS-private
COQC ?= coqc

COQFLAGS := \
	-q \
	-w -deprecated-hint-without-locality \
	-w -deprecated-instance-without-locality \
	-w -notation-incompatible-prefix \
	-w -notation-overriden \
	-w -ambiguous-paths \
	-w -redundant-canonical-projection \
	-w -cannot-define-projection \
	-require-import ExtLib.Structures.Monad \
	-R $(CRIS_DIR)/itreeS ITreeS \
	-R $(CRIS_DIR)/theories CRIS \
	-R $(CRIS_DIR)/library CRIS \
	-Q theories Workshop \
	-Q exercises WorkshopExercises \
	-Q checkpoints WorkshopCheckpoints

SOLUTION_SOURCES := \
	theories/SimulationCases.v \
	theories/CompilerPairs.v \
	theories/KVSource.v \
	theories/SortedListTarget.v \
	theories/KVSortedListProof.v

EXERCISE_SOURCES := \
	exercises/Exercise00_RocqCheck.v \
	exercises/Exercise10_SimulationCases_Start.v \
	exercises/Exercise20_CompilerPairs_Start.v \
	exercises/Exercise32_KVSortedList_Start.v

CHECKPOINT_SOURCES := \
	checkpoints/Checkpoint10_AfterFirstSimulation.v \
	checkpoints/Checkpoint20_AfterCompilerPairs.v \
	checkpoints/Checkpoint30_SortedListRelation.v \
	checkpoints/Checkpoint40_AfterGet.v \
	checkpoints/Checkpoint50_AfterPutRelation.v

WORKSHOP_SOURCES := \
	$(SOLUTION_SOURCES) \
	$(EXERCISE_SOURCES) \
	$(CHECKPOINT_SOURCES)

.PHONY: all solutions exercises checkpoints check clean

all: solutions exercises checkpoints

solutions:
	@set -e; for source in $(SOLUTION_SOURCES); do \
		echo "COQC $$source"; \
		$(COQC) $(COQFLAGS) $$source; \
	done

exercises: solutions
	@set -e; for source in $(EXERCISE_SOURCES); do \
		echo "COQC $$source"; \
		$(COQC) $(COQFLAGS) $$source; \
	done

checkpoints: solutions
	@set -e; for source in $(CHECKPOINT_SOURCES); do \
		echo "COQC $$source"; \
		$(COQC) $(COQFLAGS) $$source; \
	done

check: all
	@if grep -nE '(^|[^[:alnum:]_])(Admitted|admit)([^[:alnum:]_]|$$)' \
		$(WORKSHOP_SOURCES); then \
		echo "Unexpected admitted proof in workshop Rocq files" >&2; \
		exit 1; \
	fi

clean:
	find theories exercises checkpoints -type f \
		\( -name '*.aux' -o -name '*.glob' -o -name '*.vo' \
		-o -name '*.vok' -o -name '*.vos' -o -name '*.cache' \) \
		-delete 2>/dev/null || true
	rm -f .lia.cache .nia.cache
