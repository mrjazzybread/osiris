#!/bin/bash
set -euo pipefail

# This tests that the osiris interpreter produces the same output as ocaml on
# each of the test files

INTERP="${INTERP:-../_build/default/interp/interp.exe}"

find * -type f -name '*.ml' | while read -r f
do
    test=${f%.ml}
    echo -ne "test: $test\t"
    "$INTERP" "$test.ml" > "$test.olang"
    #./interp.exe "$test.ml" --detcheck
    ocaml "$test.ml" > "$test.ocaml"
    diff "$test.ocaml" "$test.olang" && echo ok || echo NOK
    # # to also test vs ocamlopt (takes twice as much time):
    # ocamlopt "$test.ml" -o a.out && ./a.out > "$test.ocamlopt"
    # diff "$test.ocaml" "$test.olang" || echo NOK
    rm -f a.out "$test".{o,cmi,cmo,cmx,ocaml,ocamlopt,olang}
done

# Some statistics
if ! command -v ocamlwc >/dev/null 2>&1
then
    exit 0
else
    nfiles=$(find ./* -type f -name '*.ml' | wc -l)
    nloc=$(find ./* -type f -name '*.ml' -exec ocamlwc -c {} + | tail -n1 | grep -o -P '\d*')
    echo "$nfiles files, $nloc lines of code, exluding comments"
fi
