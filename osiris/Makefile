.PHONY: all
all:
	@ dune build .

.PHONY: clean
clean:
	dune clean

# [make lint] checks that osiris.opam is well-formed.
.PHONY: lint
lint: all
	@ opam lint osiris.opam

# [make pin] installs the current version of the translator (osiris)
# into the opam switch named osiris.
# This makes sense only if this directory has been committed, I think.
# Otherwise opam will not see the changes. [opam pin -w] does not seem
# to work.
.PHONY: pin
pin: all
	@ if [ -n "$$(git status --porcelain .)" ] ; then \
	    git status . ; \
	    echo "\nCannot pin: there remain uncommitted changes." ; \
	    exit 1 ; \
	  fi
	@ opam pin --yes --switch osiris add osiris .

# [make unpin] undoes the effect of [make pin].
.PHONY: unpin
unpin:
	@ opam pin --yes --switch osiris remove osiris
