#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
: "${BASE_SOURCE_DIR:?Set BASE_SOURCE_DIR to the verified n9–13 source bundle directory.}"
BASE_SOURCE_DIR=$(cd "$BASE_SOURCE_DIR" && pwd)
: "${MATHLIB_DIR:?Set MATHLIB_DIR to the built Mathlib checkout pinned to v4.34.1.}"
MATHLIB_DIR=$(cd "$MATHLIB_DIR" && pwd)
lean_bin=${LEAN_BIN:-lean}
"$lean_bin" --version | grep -F 'version 4.34.1'
expected=d13f23b723b8a846827a245b89c10fc7d3f11612
actual=$(git -C "$MATHLIB_DIR" rev-parse HEAD)
[[ "$actual" == "$expected" ]] || { echo "Mathlib commit is $actual; expected $expected." >&2; exit 1; }
(cd "$here" && sha256sum -c SHA256SUMS)
(cd "$BASE_SOURCE_DIR" && sha256sum -c SHA256SUMS)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
export LEAN_PATH="$scratch:$MATHLIB_DIR/.lake/build/lib/lean:$(find "$MATHLIB_DIR/.lake/packages" -type d -path '*/.lake/build/lib/lean' | paste -sd ':' -)"
for src in "$BASE_SOURCE_DIR" "$here"; do
  while IFS= read -r module; do
    echo "Checking $module"
    "$lean_bin" -M "${LEAN_MEM_MIB:-3000}" --root="$src" -o "$scratch/$module.olean" "$src/$module.lean"
  done < "$src/proof-order.txt"
done
(cd "$here" && python3 audit_ext17.py)
