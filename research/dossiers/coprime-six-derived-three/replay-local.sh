#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
mathlib=$(realpath "${1:?Usage: bash replay-local.sh /path/to/compiled/mathlib4}")
: "${LEAN_BIN:?Set LEAN_BIN to Lean 4.34.1}"
v=$("$LEAN_BIN" --version)
r=$(git -C "$mathlib" rev-parse HEAD)
printf '%s\nMathlib %s\n' "$v" "$r"
[[ "$v" == "Lean (version 4.34.1,"* && "$r" == d13f23b723b8a846827a245b89c10fc7d3f11612 ]] || exit 2
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build:$mathlib/.lake/build/lib/lean"
for d in "$mathlib"/.lake/packages/*/.lake/build/lib/lean; do
  if [[ -d "$d" ]]; then LEAN_PATH="$LEAN_PATH:$d"; fi
done
while read -r part name; do
  case "$part" in
    new) src="$here" ;;
    allodd) src="$here/../all-odd-derived-two" ;;
    nonnil) src="$here/../non-nilpotent-derived-two" ;;
    ribbon) src="$here/../class-two-bicayley" ;;
    haar) src="$here/../haar-dyadic-cycles" ;;
    *) echo "Unknown source group $part" >&2; exit 1 ;;
  esac
  printf 'Checking %s\n' "$name"
  "$LEAN_BIN" --root="$src" -o "$build/${name%.lean}.olean" "$src/$name"
done < "$here/proof-order.txt"
