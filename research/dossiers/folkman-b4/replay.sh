#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
: "${MATHLIB_DIR:?Set path to built pinned Mathlib.}"
lib=$(cd "$MATHLIB_DIR" && pwd)
lean=${LEAN_BIN:-lean}
[[ $(git -C "$lib" rev-parse HEAD) == d13f23b723b8a846827a245b89c10fc7d3f11612 ]]
"$lean" --version | grep -F 'version 4.34.1'
(cd "$here" && sha256sum -c SHA256SUMS)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
export LEAN_PATH="$out:$lib/.lake/build/lib/lean:$(find "$lib/.lake/packages" -type d -path '*/.lake/build/lib/lean' | paste -sd ':' -)"
libbuild="$lib/.lake/build/lib/lean"
hall="Mathlib/Combinatorics/Hall/Finite"
if [[ ! -f "$libbuild/$hall.olean" ]]; then
  cp -as "$libbuild/Mathlib" "$out/Mathlib"
  mkdir -p "$out/$(dirname "$hall")"
  "$lean" -j1 -M2450 --root="$lib" -o "$out/$hall.olean" "$lib/$hall.lean"
fi
for n in FanoParity FanoGraph CriticalKernel CriticalCard CriticalCubic DetSign DetMatching CriticalPfaffian CriticalTransport CentralSquare MinimalFamily FamilyCore GraphBookCore BookConclusion TightDirections RegularHall TightCard TightContract TightLift TightShoreLift TightSquare TightParity TightSigning FanoLabels FanoTransfer FanoPointPort FanoLinePort TightOrient TightExpansion TightBrace TightMinimum TightMinContract TightDegrees TightCubicContraction BraceSquares; do "$lean" -j1 -M2850 --root="$here" -o "$out/$n.olean" "$here/$n.lean"; done
