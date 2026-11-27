# A tenth-power carryless cutoff example

For n = 32747 and m = 31655, the least positive index i with ordinary m × i equal to base-two carryless n ⊗ i is **749513009868723669066958919875511371508404090751**. Both products are 23725834327394447744314584608659312465098531492722905. The witness exceeds n¹⁰.

This strengthens the earlier finite ninth-power example and follows [Derek Blair's merged refutation of the cubic cutoff](https://github.com/derekblair/math-proofs/blob/ebb693747acae8f2e5b18709213ac366c1d7547f/lean/MathProofs/SeamB/C064/Solution.lean). It is not a new global conjecture result, a claim about the smallest pair (n,m), or an asymptotic lower bound.

[Exact Lean statement](C064Exact.lean). All 54 standalone modules replayed from an empty output directory in Lean 4.34.1 with Mathlib at d13f23b723b8a846827a245b89c10fc7d3f11612. The two final statements use only standard Lean axioms. The certificate uses 1,168 budgeted carry states. Independent Python checks reproduce both the least witness and 1,186 required closure transitions.

Reproduce by decoding and unpacking `certificate.tar.gz.base64` and running `MATHLIB_DIR=/path/to/mathlib LEAN_BIN=/path/to/lean bash src/replay.sh`. Run `python3 src/audit_values.py` for the independent value check and `(cd src && python3 audit_table.py)` for the closure audit. Replay this archive separately from the ninth-power archive.
