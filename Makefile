.PHONY: clean
clean::
	git clean -fX

-include Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@
