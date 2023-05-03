.PHONY: all
all:
	dune build @all --display=short

.PHONY: clean
clean:
	dune clean

.PHONY: tutorial
tutorial: all
	alectryon -R . AmpleStep tutorial/tutorial.v
