#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
mathlib="$(cd "${1:?pass the Mathlib v4.34.1 checkout path}" && pwd)"
logdir="$(realpath -m "${2:-./wow269-audit}")"
mkdir -p "$logdir"
test "$(git -C "$mathlib" rev-parse HEAD)" = d13f23b723b8a846827a245b89c10fc7d3f11612
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
mods=(Wow268 Adjacent KeepTree Core Result Refute269 Small269 Big269 C4_269 Sum269 Answer269)
for m in "${mods[@]}"; do cp "$here/$m.lean" "$build/"; done
cd "$mathlib"
lake env bash -ec '
  set -o pipefail
  d="$1"; logs="$2"; shift 2
  export LEAN_PATH="$d:$LEAN_PATH"
  lean --version | tee "$logs/toolchain.log"
  for m do
    echo "Building $m"
    lean --root="$d" -o "$d/$m.olean" "$d/$m.lean"
  done 2>&1 | tee "$logs/build.log"
  grep -F "depends on axioms:" "$logs/build.log" > "$logs/axioms.log"
  ! grep -Eq "sorryAx|ofReduceBool|Lean.ofReduceBool" "$logs/axioms.log"
  for m do
    leanchecker -v "$m"
    echo "Kernel replay passed: $m"
  done 2>&1 | tee "$logs/replay.log"
' run "$build" "$logdir" "${mods[@]}"
python "$here/Verify269.py" | tee "$logdir/independent.log"
