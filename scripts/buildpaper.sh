#!/usr/bin/env bash
# Compile the paper to PDF and report only the LaTeX errors (lines starting with '!')
# plus undefined references/citations. Usage: scripts/buildpaper.sh
set -u
cd "$(dirname "$0")/../docs" || exit 2

# The paper's verbatim Lean listing contains math Unicode, so prefer a Unicode engine
# (lualatex/xelatex); fall back to pdflatex only if those are unavailable.
engine=""
for e in lualatex xelatex pdflatex; do
  if command -v "$e" >/dev/null 2>&1; then engine="$e"; break; fi
done
if [ -z "$engine" ]; then
  echo "NO-LATEX: no lualatex/xelatex/pdflatex installed; skipping paper compile."
  exit 3
fi
echo "(engine: $engine)"

"$engine" -interaction=nonstopmode -halt-on-error UniversalityOfThreePlaceIdentity.tex \
  > /tmp/paper_build.log 2>&1
"$engine" -interaction=nonstopmode -halt-on-error UniversalityOfThreePlaceIdentity.tex \
  >> /tmp/paper_build.log 2>&1
status=$?

echo "--- LaTeX errors / undefined refs ---"
grep -nE '^!|Undefined control sequence|Undefined reference|Citation .* undefined|LaTeX Warning: Reference|LaTeX Warning: Citation' /tmp/paper_build.log \
  || echo "(none)"
echo "=== latex exit: $status ==="
exit $status
