#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
BASE_SOURCE_DIR=$(cd "${BASE_SOURCE_DIR:-$here/..}" && pwd)
: "${MATHLIB_DIR:?Set MATHLIB_DIR to compiled pinned Mathlib.}"
MATHLIB_DIR=$(cd "$MATHLIB_DIR" && pwd)
lean_bin=${LEAN_BIN:-lean}
"$lean_bin" --version | grep -F 'version 4.34.1'
[[ "$(git -C "$MATHLIB_DIR" rev-parse HEAD)" == d13f23b723b8a846827a245b89c10fc7d3f11612 ]]
for src in "$BASE_SOURCE_DIR" "$here"; do (cd "$src" && sha256sum -c SHA256SUMS); done
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
export LEAN_PATH="$scratch:$MATHLIB_DIR/.lake/build/lib/lean:$(find "$MATHLIB_DIR/.lake/packages" -type d -path '*/.lake/build/lib/lean' | paste -sd ':' -)"
for src in "$BASE_SOURCE_DIR" "$here"; do
  while IFS= read -r name; do
    printf 'Checking %s\n' "$name"
    "$lean_bin" --root="$src" -o "$scratch/$name.olean" "$src/$name.lean"
  done < "$src/proof-order.txt"
done
(cd "$here" && python3 check.py)
