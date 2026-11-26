#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
mathlib="$(cd "${1:?usage: verify.sh PATH_TO_PINNED_MATHLIB}" && pwd)"
test "$(git -C "$mathlib" rev-parse HEAD)" = d13f23b723b8a846827a245b89c10fc7d3f11612
scratch="$(mktemp -d)"
trap 'rm -rf -- "$scratch"' EXIT
cp "$here/../haar-dyadic-cycles/"*.lean "$here/"*.lean "$scratch/"
cd "$mathlib"
export LEAN_PATH="$scratch"
lake env lean --version
while IFS= read -r n; do
  lake env lean --root="$scratch" -o "$scratch/$n.olean" "$scratch/$n.lean"
  printf 'checked %s\n' "$n"
done < "$here/MODULES.txt"
