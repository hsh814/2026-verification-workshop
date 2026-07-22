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
	-require-import ExtLib.Structures.Monad

SOURCES := Behavior.v Optimizations.v KVSortedList.v

.PHONY: all check clean

all:
	@set -e; for source in $(SOURCES); do \
		echo "COQC $$source"; \
		$(COQC) $(COQFLAGS) $$source; \
	done

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
	rm -f .lia.cache .nia.cache
