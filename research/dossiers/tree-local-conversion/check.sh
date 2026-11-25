#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "$0")" && pwd)"
: "${MATHLIB_DIR:?Set MATHLIB_DIR to a cached checkout of Mathlib v4.27.0}"
cd "$MATHLIB_DIR"
lake env bash -c '
  set -euo pipefail
  cd "$1"
  export LEAN_PATH="$PWD:$LEAN_PATH"
  for f in TreeInfluenceMetric TreeInfluenceScopes TreeInfluenceDP; do
    lean -o "$f.olean" "$f.lean"
  done
' _ "$root"
