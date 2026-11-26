#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
haar=$(realpath "${2:-$here/../haar-dyadic-cycles}")
mathlib=$(realpath "${1:?Usage: bash replay-local.sh /path/to/built/mathlib4 [haar-source-dir]}")
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
cd "$mathlib"
for m in HaarCycle HaarClass3Table HaarClass3Collect HaarOrderTwo HaarAllNoncommuting HaarBound16 HaarSharpCore HaarSharpGraph HaarHalfCollision HaarClass3Collector64 HaarAbelCore HaarAbel HaarCentral HaarClass3Cycle HaarClass3Odd HaarClass4Table HaarClass4CollectCore HaarClass4Powers HaarClass4Normal HaarVoltage HaarVoltageLift HaarClass4Graph HaarClass4Projection HaarClass4Certificates HaarClass4Gate HaarClass4Prime HaarClass4Structure HaarClass4Data HaarClass4Ports HaarClass4Generate HaarTwoKernel HaarClassThreeFinite HaarClassFourFinite HaarClass3Separation64 HaarUniversal36 HaarClass5Commute; do
  lake env lean --root="$haar" -o "$build/$m.olean" "$haar/$m.lean"
done
for m in Ribbon RibbonAbelian RibbonSharp RibbonAsymm RibbonAsymmStructure RibbonClass3Data RibbonClass3 RibbonClass3SharpGraph RibbonClass3SharpHalf RibbonClass3SharpUpper RibbonClass3SharpCert RibbonClass3Sharp RibbonClass3SharpComponent RibbonClass4Data RibbonClass4Core RibbonClass4Graph RibbonClass4Ports RibbonClass4Fallback RibbonClass4Short RibbonClass4Family RibbonClass4SharpGraph RibbonClass4SharpHalf RibbonClass4SharpCert RibbonClass4SharpUpper RibbonClass4Sharp RibbonClass4SharpComponent Ribbon5LawWords Ribbon5LawAlgebra Ribbon5BridgeChart Ribbon5ChartSound Ribbon5Walk Ribbon5Bridge64 Ribbon5GeneratorDrop Ribbon5Family Ribbon6Chart Ribbon6Algebra Ribbon6Mates Ribbon6Family; do
  lake env lean --root="$here" -o "$build/$m.olean" "$here/$m.lean"
done
