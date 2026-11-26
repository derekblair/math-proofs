#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
build=$(realpath "$1")
haar=$(realpath "$2")
mathlib=$(realpath "$3")
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
cd "$mathlib"
for m in HaarClassFourOdd HaarClassFourAll HaarAnyPorts; do
  lake env lean --root="$haar" -o "$build/$m.olean" "$haar/$m.lean"
done
for m in HaarMatrixFiltration HaarMatrixRows HaarMatrixCycle HaarMatrixCard HaarMatrixClassExact HaarMatrixPacked HaarMatrixPackedSound Ribbon5UT Ribbon5Run Ribbon5Half Ribbon5Packed Ribbon5PackedSound Ribbon5PortClass Ribbon5Component Ribbon5OwnerData Ribbon5OwnerCore Ribbon5OwnerBase; do
  lake env lean --root="$here" -o "$build/$m.olean" "$here/$m.lean"
done
compile() {
  local m="$1"
  lake env lean --root="$here/owner-shards" -o "$build/$m.olean" "$here/owner-shards/$m.lean"
}
export here build
export -f compile
grep -v '^Ribbon5OwnerFinished$' "$here/owner-shard-order.txt" | xargs -P "${SHARP_JOBS:-2}" -I '{}' bash -c 'compile "$1"' _ '{}'
compile Ribbon5OwnerFinished
lake env lean --root="$here" -o "$build/Ribbon5Complete.olean" "$here/Ribbon5Complete.lean"
lake env lean --root="$here" -o "$build/Ribbon5DerivedSharp.olean" "$here/Ribbon5DerivedSharp.lean"
