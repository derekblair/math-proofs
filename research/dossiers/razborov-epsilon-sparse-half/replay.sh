#!/usr/bin/env bash
set -euo pipefail
source_dir=$(cd "$(dirname "$0")" && pwd)
: "${MATHLIB_LEAN_PATH:?Set MATHLIB_LEAN_PATH to the pinned built libraries, including dependencies}"
LEAN_BIN=${LEAN_BIN:-lean}
w=$(mktemp -d)
trap 'rm -rf "$w"' EXIT
export LEAN_PATH="$w:$MATHLIB_LEAN_PATH"
cd "$w"
modules=(ComplementCore BalancedBlockCover BicliqueKnapsack ConvexPacking LowSmallSide OutsideGreedy TwoSignatureCost TwoBlockCertificate TwoBlockChambers OneHeavyNormalized OneHeavyPacking ThreeHeavy TwoHeavyDual TwoHeavyFinish SaturatedEndpoint SaturatedOrthogonal CaseTwoDeficit ActiveProfileCap ActiveProfileCapWeighted TwoHeavyRigidity LowBalancedMass FractionalCaseTwo)
for z in "${modules[@]}"; do
  cp "$source_dir/$z.lean" .
  "$LEAN_BIN" -o "$z.olean" "$z.lean"
done
printf '\nReplayed %s modules in an isolated workspace.\n' "${#modules[@]}"
