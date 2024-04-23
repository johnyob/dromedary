.DEFAULT_GOAL := all

UNAME := $(shell uname)

.PHONY: create-switch
create-switch:
	opam switch create . 4.12.0 --no-install

.PHONY: all
all: build

.PHONY: install-native
install-native:
ifeq ($(UNAME),Linux)
	sudo apt-get update -y
	sudo apt-get install -y libgraph-easy-perl cloc
endif
ifeq ($(UNAME),Darwin)
	brew install cpanminus cloc
	cpanm Graph::Easy
endif

.PHONY: install
install: create-switch install-native
	opam install . --deps-only --with-test --with-doc

.PHONY: build
build:
	opam exec -- dune build --root .

.PHONY: test
test:
	opam exec -- dune runtest --root .

.PHONY: clean
clean:
	opam exec -- dune clean --root .

.PHONY: cloc
cloc:
	./scripts/cloc.sh

.PHONY: coverage
coverage: clean
	BISECT_ENABLE=yes opam exec -- dune build
	opam exec -- dune runtest
	opam exec -- bisect-ppx-report html
	opam exec -- bisect-ppx-report summary