#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
ROOT="$(cd ../.. && pwd)"
ML="$ROOT/toolchain/mathlib4"
BIN="$ROOT/toolchain/lean-4.34.1-linux/bin"
export PATH="$BIN:$PATH"
BASE="$(cd "$ML" && lake env printenv LEAN_PATH)"
export LEAN_PATH="$(pwd):$(cd "$ML" && printf '%s' "$BASE" | tr ':' '\n' | sed "s@^\./@$ML/@" | paste -sd ':' -)"
for m in "${@:-RamseySmall}"; do lean -j1 -o "$m.olean" "$m.lean"; done
