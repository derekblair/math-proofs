#!/usr/bin/env bash
set -euo pipefail
: "${LEAN:?set LEAN to the pinned Lean executable}"
: "${MATHLIB:?set MATHLIB to the built pinned Mathlib checkout}"
cd "$(dirname "$0")"
dep="$(find "$MATHLIB/.lake/packages" -type d -path '*/.lake/build/lib/lean' | paste -sd:)"
export LEAN_PATH="$PWD:$MATHLIB/.lake/build/lib/lean:$dep"
for m in BoxCore BoxClip ClipProgress BoxExit BoxBudget BoxAverage BoxShrink FiniteScale ShrinkHorizon RankCuts BoxRoster RosterTree BoxToken FlowPaths; do
  "$LEAN" -o "$m.olean" "$m.lean"
done
