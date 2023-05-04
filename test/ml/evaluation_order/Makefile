.PHONY: test
test:
	ocaml evaluation_order.ml > bytecode.out
	ocamlopt evaluation_order.ml && ./a.out > native.out
	diff bytecode.out native.out
	cat bytecode.out

.PHONY: clean
clean:
	git clean -fX .
