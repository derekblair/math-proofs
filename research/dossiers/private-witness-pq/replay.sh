#!/usr/bin/env bash
set -euo pipefail
: "${LEAN_BIN:?path to Lean 4.34.1}"
: "${MATHLIB_ROOT:?path to built Mathlib v4.34.1}"
dir="$(cd "$(dirname "$0")" && pwd)"
build="$(mktemp -d)"
trap 'rm -rf -- "$build"' EXIT
cp "$dir/"*.lean "$build/"
cd "$build"
export LEAN_PATH="$PWD:$MATHLIB_ROOT/.lake/build/lib/lean:$(find "$MATHLIB_ROOT/.lake/packages" -type d -path '*/.lake/build/lib/lean' | paste -sd:)"
for m in HittingAlteration CatalogBound BlindWitness; do
  "$LEAN_BIN" -o "$m.olean" "$m.lean"
done
python3 "$dir/checks.py"
python3 "$dir/baseline/check.py"
python3 "$dir/witness_coverage_check.py"
