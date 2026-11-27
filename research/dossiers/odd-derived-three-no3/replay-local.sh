#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
mathlib=$(realpath "${1:?Usage: bash replay-local.sh /path/to/compiled/mathlib4}")
: "${LEAN_BIN:?Set LEAN_BIN to Lean 4.34.1}"
v=$("$LEAN_BIN" --version)
r=$(git -C "$mathlib" rev-parse HEAD)
printf '%s\nMathlib %s\n' "$v" "$r"
[[ "$v" == "Lean (version 4.34.1,"* && "$r" == d13f23b723b8a846827a245b89c10fc7d3f11612 ]] || exit 2
if [[ -n "${REPLAY_OUTPUT:-}" ]]; then
    mkdir -p "$REPLAY_OUTPUT"
    build=$(realpath "$REPLAY_OUTPUT")
else
    build=$(mktemp -d)
    trap 'rm -rf "$build"' EXIT
fi
export LEAN_PATH="$build:$mathlib/.lake/build/lib/lean"
for pkg in "$mathlib"/.lake/packages/*/.lake/build/lib/lean; do
  if [[ -d "$pkg" ]]; then LEAN_PATH="$LEAN_PATH:$pkg"; fi
done
while read -r part name; do
  if [[ "$part" == new ]]; then src="$here"; else src="$here/../$part"; fi
  printf 'Checking %s\n' "$name"
  obj="$build/${name%.lean}.olean"
  if [[ -f "$obj" && "${RESUME_UNCHANGED:-0}" == 1 ]]; then continue; fi
  "$LEAN_BIN" --root="$src" -o "$obj" "$src/$name"
done < "$here/proof-order.txt"
