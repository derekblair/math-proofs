#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
mathlib=$(realpath "${1:?Usage: bash replay-local.sh /path/to/mathlib4 [ribbon-source-dir] [haar-source-dir]}")
ribbon=$(realpath "${2:-$here/../class-two-bicayley}")
haar=$(realpath "${3:-$here/../haar-dyadic-cycles}")
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
cd "$mathlib"
while read -r part name; do
  case "$part" in
    new) src="$here" ;;
    ribbon) src="$ribbon" ;;
    haar) src="$haar" ;;
    *) printf 'Unknown source kind: %s\n' "$part" >&2; exit 1 ;;
  esac
  printf 'Checking %s\n' "$name"
  lake env lean --root="$src" -o "$build/${name%.lean}.olean" "$src/$name"
done < "$here/proof-order.txt"
