#!/usr/bin/env bash
set -euo pipefail
this=$(cd "$(dirname "$0")" && pwd)
dossier=$(dirname "$this")
: "${MATHLIB_LEAN_PATH:?Set pinned Mathlib and package Lean search paths}"
lean_bin=${LEAN_BIN:-lean}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
export LEAN_PATH="$work:$MATHLIB_LEAN_PATH"
cd "$work"
count=0
while IFS= read -r relative; do
  [[ -n "$relative" ]] || continue
  name=$(basename "$relative" .lean)
  cp "$dossier/$relative" "$name.lean"
  echo "Checking $relative"
  "$lean_bin" -o "$name.olean" "$name.lean"
  count=$((count+1))
done < "$this/full-proof-order.txt"
printf 'Replayed %s proof dependencies, including RazborovEpsilon\n' "$count"
