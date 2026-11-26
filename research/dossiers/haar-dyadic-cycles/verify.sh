#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
mathlib="$(cd "${1:?usage: verify.sh PATH_TO_PINNED_MATHLIB}" && pwd)"
case "$(git -C "$mathlib" rev-parse HEAD)" in
  d13f23b723b8a846827a245b89c10fc7d3f11612) ;;
  *) echo "Expected the pinned mathlib revision" >&2; exit 1;;
esac
scratch="$(mktemp -d)"
trap 'rm -rf -- "$scratch"' EXIT
cp "$here/"*.lean "$scratch/"
cd "$mathlib"
export LEAN_PATH="$scratch"
lake env lean --version
for module in HaarCycle HaarOrderTwo HaarAllNoncommuting HaarBound16 HaarAbelCore HaarAbel HaarSharpCore HaarSharpGraph HaarCentral HaarClass3Table HaarClass3Collect HaarClass3Cycle HaarClass3Odd HaarClass4Table HaarClass4CollectCore HaarClass4Powers HaarClass4Normal HaarVoltage HaarVoltageLift HaarClass4Graph HaarClass4Projection HaarClass4Certificates HaarClass4Gate HaarClass4Prime HaarClass4Structure HaarClass4Data HaarClass4Ports HaarClass4Generate HaarTwoKernel HaarClassThreeFinite HaarClassFourFinite HaarClassFourOdd HaarClassFourAll HaarAnyPorts HaarHalfCollision HaarReducedWalkCycle HaarShortClosedIsCycle HaarUniversal36 HaarClass5GirthUpper HaarClass5Commute HaarClass5DyadicHighGirth HaarClass5AnyPorts HaarClass3Collector64 HaarClass3Separation64 HaarClass5L2Abelian HaarClass5DirectionCover HaarClass5DirTables HaarClass5TemplateClosure HaarClass5DirPair0 HaarClass5DirPair1 HaarClass5DirPair2 HaarClass5DirPair3 HaarClass5DirPairs HaarClass5TemplateCycles HaarClass5OddNoThree HaarClass5FiniteNoThree; do
  lake env lean --root="$scratch" -o "$scratch/$module.olean" "$scratch/$module.lean"
  printf 'checked %s\n' "$module"
done
