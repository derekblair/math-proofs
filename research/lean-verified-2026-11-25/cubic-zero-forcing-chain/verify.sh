#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
mathlib="$(cd "${1:?pass the Mathlib v4.34.1 checkout path}" && pwd)"
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
cp "$here"/*.lean "$build"/
cd "$mathlib"
lake env bash -ec '
  d="$1"
  export LEAN_PATH="$d:$LEAN_PATH"
  for m in ChainLocal Interface Chain Topology DomLower DomUpper ForceUpper Shape ExactChain; do
    lean --root="$d" -o "$d/$m.olean" "$d/$m.lean"
  done
  for m in NegativeDom NegativeZF; do
    if lean --root="$d" "$d/$m.lean" > "$d/$m.log" 2>&1; then
      echo "False formula unexpectedly accepted: $m" >&2
      exit 1
    fi
    grep -q "error:" "$d/$m.log"
    grep -q "is false" "$d/$m.log"
    echo "Expected rejection: $m"
  done
' verify "$build"
