#!/usr/bin/env bash
# Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52
# Mathlib commit d13f23b723b8a846827a245b89c10fc7d3f11612
set -euo pipefail
this=$(cd "$(dirname "$0")" && pwd)
: "${MATHLIB_LEAN_PATH:?Set pinned Mathlib and package Lean search paths}"
lean_bin=${LEAN_BIN:-lean}
temp=$(mktemp -d)
trap 'rm -rf "$temp"' EXIT
cp "$this/DirectedAnchorCounting.lean" "$temp/"
cd "$temp"
export LEAN_PATH="$temp:$MATHLIB_LEAN_PATH"
"$lean_bin" -o DirectedAnchorCounting.olean DirectedAnchorCounting.lean
