#!/usr/bin/env bash
set -euo pipefail
src="$(cd "$(dirname "$0")" && pwd)"
lib="$(cd "${1:?pass an official mathlib4 v4.34.1 checkout with cached imports}" && pwd)"
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT
cp "$src"/{Window,Witness,Templates,Counts,Statement,IrrAnalytic,IrrMasks,IrrCount,IrrMarked,IrrFinal}.lean "$scratch"
cd "$lib"
lake env bash -c '
  set -euo pipefail
  scratch="$1"
  export LEAN_PATH="$scratch:${LEAN_PATH:-}"
  cd "$scratch"
  for f in Window Witness Templates Counts Statement IrrAnalytic IrrMasks IrrCount IrrMarked IrrFinal; do
    lean -o "$f.olean" "$f.lean"
  done
  sed "s/def q2143 : Perm 4 := swPerm doubleDimer/def q2143 : Perm 4 := swPerm (mEmpty 4)/" IrrMarked.lean > RedQ.lean
  if lean RedQ.lean > red-q.log 2>&1; then exit 1; fi
  grep -E "error:.*decide" red-q.log >/dev/null
  echo "Negative control: replacing 2143 with 1234 was rejected"
  printf "%s\n" "import IrrCount" "open FibPopularity" "example : Fintype.card (Mask 4) = 6 := by rw [card_mask]; decide" > RedCount.lean
  if lean RedCount.lean > red-count.log 2>&1; then exit 1; fi
  grep -E "error:.*decide" red-count.log >/dev/null
  echo "Negative control: the wrong class cardinality at n=4 was rejected"
' _ "$scratch"
python3 "$src/irr-cert.py"
