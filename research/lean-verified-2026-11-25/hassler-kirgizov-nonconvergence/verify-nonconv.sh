#!/usr/bin/env bash
set -euo pipefail
src="$(cd "$(dirname "$0")" && pwd)"
lib="$(cd "${1:?pass an official mathlib4 v4.34.1 checkout with cached imports}" && pwd)"
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT
cp "$src"/{Window,Witness,Templates,Counts,Statement,NonconvData,NonconvLocal,NonconvCounts,NonconvRealize,NonconvWalk,NonconvSource,NonconvMarked,NonconvFinal}.lean "$scratch"
cd "$lib"
lake env bash -c '
  set -euo pipefail
  scratch="$1"
  export LEAN_PATH="$scratch:${LEAN_PATH:-}"
  cd "$scratch"
  for f in Window Witness Templates Counts Statement NonconvData NonconvLocal NonconvCounts NonconvRealize NonconvWalk NonconvSource NonconvMarked NonconvFinal; do
    lean -o "$f.olean" "$f.lean"
  done
  printf "%s\n" "import NonconvFinal" "open Nonconv" \
    "example : totalRoutes 0 = 45 := by rw [route_bases.1]; decide" > RedCount.lean
  if lean RedCount.lean > red-count.log 2>&1; then exit 1; fi
  grep -E "error:.*decide" red-count.log >/dev/null
  echo "Negative control: wrong initial class size rejected"
  printf "%s\n" "import NonconvFinal" "open Nonconv" \
    "example : marks 1 = 1 := by rw [show marks 1 = 2 by decide]; decide" > RedMark.lean
  if lean RedMark.lean > red-mark.log 2>&1; then exit 1; fi
  grep -E "error:.*decide" red-mark.log >/dev/null
  echo "Negative control: wrong initial marked occurrence count rejected"
' _ "$scratch"
python3 "$src/nonconv.py"
