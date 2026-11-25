#!/usr/bin/env bash
set -euo pipefail
src="$(cd "$(dirname "$0")" && pwd)"
mathlib="$(cd "${1:?pass a Mathlib v4.34.1 checkout}" && pwd)"
result="$(realpath -m "${2:-./verification}")"
mkdir -p "$result"
test "$(git -C "$mathlib" rev-parse HEAD)" = d13f23b723b8a846827a245b89c10fc7d3f11612
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
modules=(Packing Permutation Cardinal Limit Clip Rotation PlaneMeasure FiniteIndices CellSets RotateMeasure CellArrangement IntegerBasis ApproxRows Gauge OrientedLattice DetBound Upper HexMeasure PackingGeometry LowerBound HexDensity HexLimit LiteralHex)
for m in "${modules[@]}"; do
  if [[ -r "$src/$m.lean" ]]; then cp "$src/$m.lean" "$build/"
  else cp "$src/../permcircles/$m.lean" "$build/"
  fi
done
(cd "$mathlib" && lean --version > "$result/toolchain.log")
(cd "$mathlib" && LEAN_NUM_THREADS=1 lake build Mathlib.Analysis.SpecialFunctions.Integrals.Basic Mathlib.MeasureTheory.Integral.Prod Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar) >"$result/dependencies.log" 2>&1
export LEAN_PATH="$build:$mathlib/.lake/build/lib/lean"
for p in "$mathlib"/.lake/packages/*/.lake/build/lib/lean; do LEAN_PATH="$LEAN_PATH:$p"; done
for m in "${modules[@]}"; do
  echo "Build $m"
  lean -j1 --root="$build" -o "$build/$m.olean" "$build/$m.lean"
done 2>&1 | tee "$result/build.log"
grep -F 'depends on axioms:' "$result/build.log" > "$result/axioms.log"
awk '
/depends on axioms:/ {
  s=$0
  sub(/^.*depends on axioms: *\[/,"",s)
  sub(/\].*$/,"",s)
  l=split(s,arr,/, */)
  for (i=1;i<=l;i++) if(arr[i]!="propext" && arr[i]!="Classical.choice" && arr[i]!="Quot.sound") { print "Unexpected axiom " arr[i]; bad=1 }
}
END { exit bad }
' "$result/axioms.log"
for m in "${modules[@]}"; do
  leanchecker -v "$m"
  echo "Kernel replay passed: $m"
done 2>&1 | tee "$result/replay.log"
