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
for module in HaarCycle HaarOrderTwo HaarAllNoncommuting HaarBound16 HaarAbelCore HaarAbel HaarSharpCore HaarSharpGraph HaarCentral HaarClass3Table HaarClass3Collect HaarClass3Cycle HaarClass3Odd HaarClass4Table HaarClass4CollectCore HaarClass4Powers HaarClass4Normal HaarVoltage HaarVoltageLift HaarClass4Graph HaarClass4Projection HaarClass4Certificates HaarClass4Gate HaarClass4Prime HaarClass4Structure HaarClass4Data HaarClass4Ports HaarClass4Generate HaarTwoKernel HaarClassThreeFinite HaarClassFourFinite HaarClassFourOdd HaarClassFourAll HaarAnyPorts HaarHalfCollision HaarReducedWalkCycle HaarShortClosedIsCycle HaarUniversal36 HaarClass5GirthUpper HaarClass5Commute HaarClass5DyadicHighGirth HaarClass5AnyPorts HaarClass3Collector64 HaarClass3Separation64 HaarClass5L2Abelian HaarClass5DirectionCover HaarClass5DirTables HaarClass5TemplateClosure HaarClass5DirPair0 HaarClass5DirPair1 HaarClass5DirPair2 HaarClass5DirPair3 HaarClass5DirPairs HaarClass5TemplateCycles HaarClass5OddNoThree HaarClass5FiniteNoThree HaarP3Words HaarP3Class4Collect HaarP3Class4Cases HaarP3Class4Rows HaarP3Class4Pair0 HaarP3Class4Pair1 HaarP3Class4Pair2 HaarP3Class4Pair3 HaarP3Class4Pairs HaarP3Class4Interpret HaarP3Class4Order HaarP3Class4Graph HaarP3LayerGen HaarP3LayerGenQuot HaarP3LayerGenPivot HaarP3LayerGenModels HaarP3LayerGenBridge HaarP3Class4Dispatch HaarP3LayerGenFifth HaarP3LayerGenExpo HaarP3LayerGenConcrete HaarP3FifthData HaarP3CollectCore HaarP3CollectActions HaarP3FifthLaws HaarP3Char HaarP3CharKernel HaarP3CharExceptional HaarP3FifthCharacter HaarP3FifthModelBridge HaarClass5P3MetaCore HaarClass5P3MetaModel HaarP3ExceptionalFinishCore HaarClass5P3MetaSteps HaarClass5P3MetaCycle HaarP3ExceptionalFinish HaarP3CollectSteps HaarMatrixPacked HaarMatrixPackedCheck HaarP3FifthCertCore HaarP3FifthCert01 HaarP3FifthCert02 HaarP3FifthCert10 HaarP3FifthCert11 HaarP3FifthCert12 HaarP3FifthCert20 HaarP3FifthCert21 HaarP3FifthCert22 HaarP3FifthCertData HaarP3FifthCertCycle HaarP3FifthCertIntegration HaarP3TailSeparate HaarP3TailSeparateQuot HaarP3FifthDispatch HaarP3RankSplit HaarClass5Odd HaarClass5Finite; do
  lake env lean --root="$scratch" -o "$scratch/$module.olean" "$scratch/$module.lean"
  printf 'checked %s\n' "$module"
done
