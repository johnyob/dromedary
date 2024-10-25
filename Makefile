.DEFAULT_GOAL := all

.PHONY: all
all: build

.PHONY: build
build:
	dune build --root .

.PHONY: test
test:
	dune runtest --root .

.PHONY: clean
clean:
	dune clean --root .

.PHONY: cloc
cloc:
	./scripts/cloc.sh

.PHONY: coverage
coverage: clean
	BISECT_ENABLE=yes dune build
	dune runtest
	bisect-ppx-report html
	bisect-ppx-report summary