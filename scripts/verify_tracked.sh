#!/usr/bin/env bash
# Verify that every `import UniversalityTheorem.X` resolves to a git-TRACKED file, so a
# fresh clone builds (guards against the imported-but-untracked-module class of bug).
set -u
cd "$(dirname "$0")/.." || exit 2

missing=0
imports="$(grep -rhoE 'import UniversalityTheorem\.[A-Za-z_]+' UniversalityTheorem.lean UniversalityTheorem/*.lean | sort -u)"

while read -r _kw mod; do
  [ -z "$mod" ] && continue
  rel="${mod#UniversalityTheorem.}"
  path="UniversalityTheorem/${rel}.lean"
  if git ls-files --error-unmatch "$path" >/dev/null 2>&1; then
    echo "OK   $mod"
  else
    echo "MISSING (untracked): $mod -> $path"
    missing=1
  fi
done <<EOF
$imports
EOF

if [ "$missing" -ne 0 ]; then
  echo "FAIL: some imported modules are not tracked."
  exit 1
fi
echo "OK: all imported modules are tracked."
