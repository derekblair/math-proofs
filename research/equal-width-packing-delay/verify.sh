#!/usr/bin/env bash
set -euo pipefail
src="$(cd "$(dirname "$0")" && pwd)"
ml="$(cd "${1:?Pass the Mathlib v4.34.1 checkout}" && pwd)"
result="$(realpath -m "${2:-./verification}")"
mkdir -p "$result"
test "$(git -C "$ml" rev-parse HEAD)" = d13f23b723b8a846827a245b89c10fc7d3f11612
lean --version | tee "$result/toolchain.log" | grep -q 'version 4.34.1'
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
mapfile -t older_cutoff < "$src/cutoff-dependencies.txt"
mapfile -t older_dyck < "$src/dyck-dependencies.txt"
mapfile -t own < "$src/modules.txt"
shared="$src/../lean-verified-2026-11-25"
for m in "${older_cutoff[@]}"; do cp "$shared/bks-packing-cutoff/$m.lean" "$build/"; done
for m in "${older_dyck[@]}"; do cp "$shared/bks-uniform-catalan/$m.lean" "$build/"; done
for m in "${own[@]}"; do cp "$src/$m.lean" "$build/"; done
modules=("${older_cutoff[@]}" "${older_dyck[@]}" "${own[@]}")
(cd "$ml" && LEAN_NUM_THREADS=1 lake build Mathlib.Combinatorics.Enumerative.DyckWord Mathlib.Data.Fin.Tuple.Take Mathlib.Data.Finset.Sort Mathlib.Data.List.NodupEquivFin Mathlib.Data.Fin.Tuple.Basic Mathlib.Data.Fintype.Sort Mathlib.Data.Prod.Lex Mathlib.Tactic) > "$result/dependencies.log" 2>&1
export LEAN_PATH="$build:$ml/.lake/build/lib/lean"
for p in "$ml"/.lake/packages/*/.lake/build/lib/lean; do LEAN_PATH="$LEAN_PATH:$p"; done
for m in "${modules[@]}"; do
  echo "Build $m"
  lean -j1 --root="$build" -o "$build/$m.olean" "$build/$m.lean"
done 2>&1 | tee "$result/build.log"
grep -F 'depends on axioms:' "$result/build.log" > "$result/axioms.log"
awk '/depends on axioms:/ {
  sub(/^.*depends on axioms: *\[/,""); sub(/\].*$/,"");
  n=split($0,a,/, */);
  for(i=1;i<=n;i++) if(a[i]!="propext" && a[i]!="Classical.choice" && a[i]!="Quot.sound") {print "Unexpected axiom",a[i]; bad=1}
}
END{ exit bad }' "$result/axioms.log"
for m in "${modules[@]}"; do
  leanchecker -v "$m"
  echo "Kernel replay passed: $m"
done 2>&1 | tee "$result/replay.log"
