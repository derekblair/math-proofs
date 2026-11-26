#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
m=$(realpath "${MATHLIB_DIR:?Provide the compiled Mathlib checkout}")
L="${LEAN_BIN:?Provide Lean 4.34.1}"
v=$("$L" --version)
r=$(git -C "$m" rev-parse HEAD)
printf '%s\nMathlib %s\n' "$v" "$r"
[[ "$v" == "Lean (version 4.34.1,"* && "$r" == d13f23b723b8a846827a245b89c10fc7d3f11612 ]] || exit 2
export LEAN_PATH="$m/.lake/build/lib/lean"
for dep in "$m"/.lake/packages/*/.lake/build/lib/lean; do
  if [[ -d "$dep" ]]; then LEAN_PATH="$LEAN_PATH:$dep"; fi
done
"$L" --root="$here" "$here/ManyFamilies.lean"
python3 "$here/checks.py"
