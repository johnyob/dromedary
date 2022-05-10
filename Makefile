default:
	opam update
	opam install . --deps-only
	dune build

build:
	dune build

install:
	opam update
	opam install . --deps-only
	sudo apt-get install -y libgraph-easy-perl

test:
	dune runtest

clean:
	dune clean

cloc:
	./scripts/cloc.sh

coverage:
	make clean
	BISECT_ENABLE=yes dune build
	dune runtest
	bisect-ppx-report html
	bisect-ppx-report summary