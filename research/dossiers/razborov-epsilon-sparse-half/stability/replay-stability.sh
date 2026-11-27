#!/usr/bin/env bash
set -euo pipefail
d=$(cd "$(dirname "$0")" && pwd)
: "${MATHLIB_LEAN_PATH:?Set the search path to the pinned built library and its dependencies}"
l=${LEAN_BIN:-lean}
w=$(mktemp -d)
trap 'rm -rf "$w"' EXIT
export LEAN_PATH="$w:$MATHLIB_LEAN_PATH"
cd "$w"
mods=(PetersenArithmetic PetersenCharts PetersenHalves PetersenCost PetersenUniform StabilityTemplates StabilityMatching StabilityCounting StabilityLoss StabilityDisturbed StabilityRepair StabilityRelabel StabilityRepaired StabilityEditTemplate StabilityLift StabilityHalfTransfer C5Uniform StabilityLocal StabilityExamples StabilityDirected)
for z in "${mods[@]}";do
  cp "$d/$z.lean" .
  "$l" -o "$z.olean" "$z.lean"
done
printf 'Replayed %s actual stability modules\n' "${#mods[@]}"
