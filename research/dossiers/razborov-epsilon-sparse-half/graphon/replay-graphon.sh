#!/usr/bin/env bash
set -euo pipefail
d=$(cd "$(dirname "$0")" && pwd)
: "${MATHLIB_LEAN_PATH:?Set the search path to the pinned built library and its dependencies}"
l=${LEAN_BIN:-lean}
w=$(mktemp -d)
trap 'rm -rf "$w"' EXIT
export LEAN_PATH="$w:$MATHLIB_LEAN_PATH"
cd "$w"
mods=(GraphonMantel ComplementRowsAE CutRowControl CutFractionalTest CutEnergy HalfCutContinuity IndependentRowsAE TriangleCutContinuity CutBinaryTemplate ReweightedEnergy EnergyAlgebra GraphonCaseTwoLocal KernelPullback GraphonCaseTwoAverage GraphonCaseTwoMarginals GraphonCaseTwo)
for z in "${mods[@]}";do
  cp "$d/$z.lean" .
  "$l" -o "$z.olean" "$z.lean"
done
printf 'Replayed %s actual graphon modules\n' "${#mods[@]}"
