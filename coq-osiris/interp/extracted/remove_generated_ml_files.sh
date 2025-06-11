#!/bin/bash

# Executing by hand the Extraction command in extract.v generates many files
# that pollute this directory.  Using make/dune is fine.

# This script removes the generated files.

test -e extract.v || (echo "File extract.v not found, are you in the right directory? Aborting."; exit)

## list of files obtained from the output of "Separate Extraction" in rocq
rm -f \
Datatypes.ml          Datatypes.mli          \
Specif.ml             Specif.mli             \
Decimal.ml            Decimal.mli            \
Bool.ml               Bool.mli               \
Basics.ml             Basics.mli             \
Orders.ml             Orders.mli             \
List.ml               List.mli               \
BinNums.ml            BinNums.mli            \
BinPosDef.ml          BinPosDef.mli          \
BinPos.ml             BinPos.mli             \
BinNat.ml             BinNat.mli             \
BinInt.ml             BinInt.mli             \
ZArith_dec.ml         ZArith_dec.mli         \
Ascii.ml              Ascii.mli              \
String.ml             String.mli             \
base.ml               base.mli               \
Zpower.ml             Zpower.mli             \
option.ml             option.mli             \
numbers.ml            numbers.mli            \
list0.ml              list0.mli              \
countable.ml          countable.mli          \
infinite.ml           infinite.mli           \
fin_sets.ml           fin_sets.mli           \
fin_maps.ml           fin_maps.mli           \
mapset.ml             mapset.mli             \
gmap.ml               gmap.mli               \
void.ml               void.mli               \
PrimFloat.ml          PrimFloat.mli          \
Coqlib.ml             Coqlib.mli             \
Zbits.ml              Zbits.mli              \
Integers.ml           Integers.mli           \
int.ml                int.mli                \
locations.ml          locations.mli          \
syntax.ml             syntax.mli             \
notations.ml          notations.mli          \
outcome.ml            outcome.mli            \
code.ml               code.mli               \
Mergesort.ml          Mergesort.mli          \
eval.ml               eval.mli               \
step.ml               step.mli               \
Externals.ml          Externals.mli          \
Stdlib.ml             Stdlib.mli             \
DecimalString.ml      DecimalString.mli      \
run.ml                run.mli                \
strategy.ml           strategy.mli           \
