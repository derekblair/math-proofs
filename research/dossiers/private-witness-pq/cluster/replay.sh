#!/usr/bin/env bash
set -euo pipefail
: "${LEAN_BIN:?pinned Lean 4.34.1 required}"
: "${MATHLIB_ROOT:?built Mathlib v4.34.1 required}"
cd "$(dirname "$0")"
export LEAN_PATH="$MATHLIB_ROOT/.lake/build/lib/lean:$(find "$MATHLIB_ROOT/.lake/packages" -type d -path '*/.lake/build/lib/lean' | paste -sd:)"
export PYTHONDONTWRITEBYTECODE=1
"$LEAN_BIN" EquitableCluster.lean
python3 checks.py
python3 minimax_bounded_dp.py
python3 minimax_layout_dp.py
