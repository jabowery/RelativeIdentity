#!/usr/bin/env bash
# CI regression guard: regenerate the axiom audit and fail if ANY key declaration depends
# on `sorryAx` (the project is sorry-free). Run after `lake build`.
set -u
cd "$(dirname "$0")/.." || exit 2

bash scripts/audit.sh >/dev/null 2>&1 || { echo "audit generation failed"; exit 2; }

bad="$(grep 'depends on axioms' docs/AxiomAudit.md | grep 'sorryAx')"
if [ -n "$bad" ]; then
  echo "FAIL: sorryAx found — the project must be sorry-free:"
  echo "$bad"
  exit 1
fi
echo "OK: no key declaration depends on sorryAx; the project is sorry-free."
