#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
mathlib="$(cd "${1:?usage: verify.sh PATH_TO_PINNED_MATHLIB}" && pwd)"
rev="$(git -C "$mathlib" rev-parse HEAD)"
test "$rev" = d13f23b723b8a846827a245b89c10fc7d3f11612
scratch="$(mktemp -d)"
trap 'rm -rf -- "$scratch"' EXIT
cp "$here/../haar-dyadic-cycles/"*.lean "$here/"*.lean "$here/"*.py "$scratch/"
(
  cd "$scratch"
  export HAAR_CERT_FIELD=31
  python3 class5_owner.py 9 8
  python3 class5_checks.py 9 8
  sha256sum --check --quiet "$here/GENERATED.sha256"
)
cd "$mathlib"
export LEAN_PATH="$scratch" HAAR_SCRATCH="$scratch"
lake env lean --version
check() {
  lake env lean --root="$HAAR_SCRATCH" -o "$HAAR_SCRATCH/$1.olean" "$HAAR_SCRATCH/$1.lean"
  printf 'checked %s\n' "$1"
}
export -f check
while IFS= read -r module; do check "$module"; done < "$here/PRE.txt"
xargs -n 1 -P "${HAAR_JOBS:-1}" bash -c 'check "$1"' _ < "$here/SHARDS.txt"
while IFS= read -r module; do check "$module"; done < "$here/POST.txt"
