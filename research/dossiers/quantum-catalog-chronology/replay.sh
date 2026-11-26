#!/usr/bin/env bash
set -euo pipefail
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
: "${MATHLIB_DIR:?Set MATHLIB_DIR to the compiled pinned Mathlib checkout}"
L="${LEAN_BIN:-lean}"
V="$("$L" --version)"
R="$(git -C "$MATHLIB_DIR" rev-parse HEAD)"
printf '%s\nMathlib %s\n' "$V" "$R"
[[ "$V" == "Lean (version 4.34.1,"* ]] || { echo "Expected Lean 4.34.1" >&2; exit 1; }
[[ "$R" == d13f23b723b8a846827a245b89c10fc7d3f11612 ]] || { echo "Incorrect Mathlib revision" >&2; exit 1; }
export LEAN_PATH="$MATHLIB_DIR/.lake/build/lib/lean"
for p in "$MATHLIB_DIR"/.lake/packages/*/.lake/build/lib/lean; do
  if [[ -d "$p" ]]; then LEAN_PATH="$LEAN_PATH:$p"; fi
done
"$L" --root="$D" "$D/Chronology.lean"
python3 "$D/controls.py"
