# This prevents Coq from producing stack backtraces.
export OCAMLRUNPARAM=

.PHONY: all clean

all:
	dune build --display=short

clean:
	dune clean
