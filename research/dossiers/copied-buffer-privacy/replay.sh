#!/usr/bin/env bash
# Precondition: Lean 4.34.1 and the pinned Mathlib workspace are already built.
set -euo pipefail
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BASE="$(cd "$D/../.." && pwd)"
M="${MATHLIB_DIR:-$BASE/emerging/mathlib4}"
L="${LEAN_BIN:-$BASE/toolchain/lean-4.34.1-linux/bin/lean}"
V="$("$L" --version)"
R="$(git -C "$M" rev-parse HEAD)"
printf '%s\nMathlib %s\n' "$V" "$R"
[[ "$V" == "Lean (version 4.34.1,"* ]] || { echo "Expected Lean 4.34.1" >&2; exit 1; }
[[ "$R" == d13f23b723b8a846827a245b89c10fc7d3f11612 ]] || { echo "Incorrect Mathlib revision" >&2; exit 1; }
for dep in "$M"/.lake/packages/*/.lake/build/lib/lean; do
  if [[ -d "$dep" ]]; then DEPS="${DEPS:-}:$dep"; fi
done
export LEAN_PATH="$M/.lake/build/lib/lean${DEPS:-}"
cd "$M"
"$L" --root="$D" "$D/PairCoverage.lean"
"$L" --root="$D" "$D/ShamirCatalog.lean"
python3 "$D/controls.py"
