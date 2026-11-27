#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
: "${MATHLIB_DIR:?Set MATHLIB_DIR to an already built Mathlib checkout at the pinned commit.}"
MATHLIB_DIR=$(cd "$MATHLIB_DIR" && pwd)
lean_bin=${LEAN_BIN:-lean}
"$lean_bin" --version | grep -F 'version 4.34.1'
expected=d13f23b723b8a846827a245b89c10fc7d3f11612
actual=$(git -C "$MATHLIB_DIR" rev-parse HEAD)
[[ "$actual" == "$expected" ]] || { echo "Mathlib commit is $actual; expected $expected." >&2; exit 1; }
(cd "$here" && sha256sum -c SHA256SUMS)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
export LEAN_PATH="$tmp:$MATHLIB_DIR/.lake/build/lib/lean:$(find "$MATHLIB_DIR/.lake/packages" -type d -path '*/.lake/build/lib/lean' | paste -sd ':' -)"
while IFS= read -r mod; do
  echo "Checking $mod"
  "$lean_bin" --root="$here" -o "$tmp/$mod.olean" "$here/$mod.lean"
done < "$here/proof-order.txt"
(cd "$here" && python3 check.py)
