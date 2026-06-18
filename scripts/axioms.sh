#!/usr/bin/env bash
# Print the axiom dependencies of one or more declarations via #print axioms.
#
# Usage: scripts/axioms.sh FULLY.QUALIFIED.NAME [MORE.NAMES ...]
# Example: scripts/axioms.sh UniversalityTheorem.Cell.mem_iff
set -u
cd "$(dirname "$0")/.." || exit 2

if [ "$#" -eq 0 ]; then
  echo "usage: scripts/axioms.sh NAME [NAME ...]"
  exit 2
fi

src=/tmp/lean_axioms.lean
: > "$src"
echo 'import UniversalityTheorem' >> "$src"
echo 'import UniversalityTheorem.Cell' >> "$src"
for name in "$@"; do
  echo "#print axioms $name" >> "$src"
done

lake env lean "$src" 2>&1 | grep -vE 'LEAN_PATH|^trace:'
