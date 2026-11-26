#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
mathlib=$(realpath "${1:?Usage: bash replay-local.sh /path/to/built/mathlib4}")
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
cd "$mathlib"
for m in SpanCriterion GenericVoltage PetersenDecision PetersenWalkData PetersenBaseId PetersenUniversal ShortProjection RefutationKernel PetersenSharpGraph PetersenSharpCover PetersenSharpFast PetersenSharpScan PetersenSharpWitness PetersenSharpEnd; do
  lake env lean --root="$here" -o "$build/$m.olean" "$here/$m.lean"
done
