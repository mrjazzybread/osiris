#!/bin/bash

set -e

# Define logical paths
LOGICAL_PATHS=(
  "_build/default/theories=osiris"
  "_build/default/examples=osiris.examples"
)

# Collect module names for each path
MODULES=()

for entry in "${LOGICAL_PATHS[@]}"; do
  PHYS_DIR="${entry%%=*}"
  LOGICAL_NS="${entry##*=}"

  MODS=$(find "$PHYS_DIR" -name "*.vo" | sed -e "s|$PHYS_DIR/||" -e 's|\.vo$||' -e 's|/|.|g' | sed "s|^|$LOGICAL_NS.|")
  MODULES+=($MODS)
done

# Build -R flags
R_FLAGS=()
for entry in "${LOGICAL_PATHS[@]}"; do
  PHYS_DIR="${entry%%=*}"
  LOGICAL_NS="${entry##*=}"
  R_FLAGS+=("-R" "$PHYS_DIR" "$LOGICAL_NS")
done

echo "Running rocqchk, this may take a minute or two..."
rocqchk -silent -o "${R_FLAGS[@]}" "${MODULES[@]}" 2>&1 | grep -v -E "Corelib\.Floats|Corelib\.Numbers|Stdlib\.Reals"
