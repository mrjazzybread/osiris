#!/bin/bash
set -euo pipefail

# This tests that the osiris interpreter produces the same output as ocaml on
# each of the test files

time for f in *.ml
do
    test=${f%.ml}
    echo -ne "test: $test\t"
    ./interp.exe $test.ml > $test.olang
    rm -f $test.ml.cmi # TODO make this unnecessary then remove
    ocaml $test.ml > $test.ocaml
    diff $test.ocaml $test.olang && echo ok || echo NOK
    rm -f $test.ocaml $test.olang
done
