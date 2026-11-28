#!/usr/bin/env bash
set -euo pipefail
src="$(cd -- "$(dirname -- "$0")" && pwd)"
: "${LEAN_BIN:?set to Lean 4.34.1 executable}"
: "${MATHLIB_ROOT:?set to configured Mathlib v4.34.1 checkout}"
build="${UNBLOCKING_BUILD:-$(mktemp -d)}"
mkdir -p "$build"
cd "$build"
build="$PWD"
export LEAN_PATH="$build:$MATHLIB_ROOT/.lake/build/lib/lean:$(find "$MATHLIB_ROOT/.lake/packages" -type d -path '*/.lake/build/lib/lean' | paste -sd:)"
mods=(Degree10Unblocking UnblockingGraph UnblockingIncidence UnblockingLocal UnblockingLower UnblockingOwners UnblockingPools)
for m in RamseySmall RamseyExactNine PrivatePools; do mods+=("lean-ramsey-agent/$m"); done
for m in UpperIncidence UnblockedCard; do mods+=("lean-upper-agent/$m"); done
mods+=(UnblockingRowCaps UnblockingOutside UnblockingExterior UnblockingDescent)
while read -r m; do mods+=("lean-bikov-agent/$m"); done < "$src/lean-bikov-agent/proof-order.txt"
mods+=(UnblockingTheorem lean-upper-agent/MaximalClique lean-ramsey-agent/RamseyPullback)
while read -r m; do
  [[ "$m" == RamseySmall ]] || mods+=("lean-ramsey-agent/$m")
done < "$src/lean-ramsey-agent/exoo-order.txt"
mods+=(Erdos151K4FreeEleven)
for m in "${mods[@]}"; do
  name="${m##*/}"
  cp "$src/$m.lean" "$name.lean"
  "$LEAN_BIN" -o "$name.olean" "$name.lean" > "$name.log" 2>&1 || { cat "$name.log"; exit 1; }
  if grep -E 'sorryAx|uses .sorry.|ofReduceBool|Lean.trustCompiler' "$name.log"; then exit 1; fi
  echo "verified $name"
done
cat UnblockingTheorem.log Erdos151K4FreeEleven.log
echo "verified ${#mods[@]} modules: $build"
