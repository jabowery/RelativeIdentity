#!/usr/bin/env bash
# Build one or more Lean targets and show only the meaningful diagnostics
# (errors, warnings, unsolved goals, sorry), suppressing LEAN_PATH/trace noise
# and the harmless "namespace 'Cell' is duplicated" / show-linter chatter.
#
# Usage: scripts/check.sh [TARGET ...]
#   default TARGET: UniversalityTheorem.Cell
set -u
cd "$(dirname "$0")/.." || exit 2

targets=("$@")
if [ "${#targets[@]}" -eq 0 ]; then
  targets=("UniversalityTheorem.Cell")
fi

lake build "${targets[@]}" > /tmp/lean_build.log 2>&1
status=$?

grep -nE 'error|warning|unsolved|sorry|Built |declaration uses' /tmp/lean_build.log \
  | grep -vE "LEAN_PATH|namespace 'Cell' is duplicated|show tactic should only|change instead|for these purposes|However, this tactic" \
  || echo "(no diagnostics)"

echo "=== lake build exit: $status ==="
exit $status
