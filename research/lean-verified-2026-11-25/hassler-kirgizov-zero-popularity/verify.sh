#!/usr/bin/env bash
# Run with Lean 4.34.1 available, and an official mathlib4 v4.34.1 checkout
# supplied as argument 1. The checkout must already have the imports cached.
set -euo pipefail
src="$(cd "$(dirname "$0")" && pwd)"
lib="$(cd "${1:?pass the path to a v4.34.1 mathlib4 checkout}" && pwd)"
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT
cp "$src"/{Window,Witness,Templates,Counts,Statement}.lean "$scratch/"
cd "$lib"
lake env bash -c '
  set -euo pipefail
  scratch="$1"
  export LEAN_PATH="$scratch:${LEAN_PATH:-}"
  cd "$scratch"
  for f in Window Witness Templates Counts Statement; do
    lean -o "$f.olean" "$f.lean"
  done
  # Reject a weakened overlap table that incorrectly omits a genuine edge.
  sed "s/(v.val = 0 ∨ v.val = 1)/(v.val = 0)/" Window.lean > RedOverlap.lean
  if lean RedOverlap.lean > overlap.negative 2>&1; then exit 1; fi
  grep -E "^is false$" overlap.negative >/dev/null
  echo "Negative control: false overlap table rejected"
  # Check that the actual computed limit is not interchangeable with 1/7.
  sed "s/(𝓝 (1\/6 : ℝ)) := by/(𝓝 (1\/7 : ℝ)) := by/" Statement.lean > RedLimit.lean
  if lean RedLimit.lean > limit.negative 2>&1; then exit 1; fi
  grep "error:" limit.negative >/dev/null
  echo "Negative control: incorrect 1/7 limit rejected"
' _ "$scratch"
python3 "$src/cert.py"
