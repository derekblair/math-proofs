# Replay the exact exposure bound

Use Lean 4.34.1 and Mathlib v4.34.1 (commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`). Build Mathlib dependencies first.
From this directory, set `LEAN_PATH` to include the current directory and
the Mathlib and dependency build directories. Then run:

```sh
set -e
for m in NestedExposureCore NestedExposureSound NestedExposureFast \
  NestedAsymBranch NestedTwoModeBound NestedFirst{00..13} NestedAsymmetricFinal
do
  lean -o "$m.olean" "$m.lean"
done
```

The final theorem `NestedExposure.exact_padded_asym_probability` checks
the worst-case probability lower bound for all labelled count vectors at
exactly 63 exposures, without relying on an assumption that those vectors
are sorted. The two active count vectors and the exact proof multiplier are
checked in `NestedTwoModeBound.lean`. The rows are calculated by the Lean
kernel in small shards; the final theorem uses only the three standard
Mathlib axioms. Padding fewer than 63 exposures, the outage argument, and
the game reduction remain paper arguments. The symmetric comparison is
checked by two exact Python scripts, not by this Lean replay.
