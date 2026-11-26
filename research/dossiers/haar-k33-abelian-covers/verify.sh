#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
mathlib="$(cd "${1:?usage: verify.sh PATH_TO_PINNED_MATHLIB}" && pwd)"
test "$(git -C "$mathlib" rev-parse HEAD)" = d13f23b723b8a846827a245b89c10fc7d3f11612
scratch="$(mktemp -d)"
trap 'rm -rf -- "$scratch"' EXIT
cp "$here/"*.lean "$scratch/"
for n in HaarCycle HaarOrderTwo HaarAllNoncommuting HaarAbelCore HaarAbel; do cp "$here/../haar-dyadic-cycles/$n.lean" "$scratch/"; done
cd "$mathlib"
export LEAN_PATH="$scratch" HAAR_SCRATCH="$scratch"
lake env lean --version
check(){
  lake env lean --root="$HAAR_SCRATCH" -o "$HAAR_SCRATCH/$1.olean" "$HAAR_SCRATCH/$1.lean"
  printf 'checked %s\n' "$1"
}
export -f check
for n in HaarCycle HaarOrderTwo HaarAllNoncommuting HaarK33Voltage HaarK33DAG HaarK33Data; do check "$n"; done
printf '%s\n' "$scratch"/HaarK33C[0-9][0-9][0-9].lean | sed -E 's#^.*/(.*)\.lean$#\1#' | xargs -n 1 -P "${HAAR_JOBS:-1}" bash -c 'check "$1"' _
for n in HaarK33Complete HaarK33Gauge HaarK33OddCover HaarK33Haar HaarAbelCore HaarAbel HaarK33CollapseCore HaarK33Collapse HaarK33AllPorts; do check "$n"; done
