# An exact ninth-power carryless cutoff example

For n = 8179 and m = 7935, the least positive **i** for which
ordinary m × i equals the base-two carryless product n ⊗ i is

**10818005328236238993612085342811863575**.

It is greater than 8179⁹. Both products are 85840872279554556414311897195212137467625.
This is a stronger finite example following [Derek Blair's merged Lean refutation of Karttunen's cubic cutoff](https://github.com/derekblair/math-proofs/blob/ebb693747acae8f2e5b18709213ac366c1d7547f/lean/MathProofs/SeamB/C064/Solution.lean). It does not assert that n or m is globally minimal or settle an asymptotic bound.

[C064Exact.lean](C064Exact.lean) proves the exact least positive solution and the ninth-power exclusion. The standalone certificate checks 624 carry states against exact remaining input budgets. Proofs use the Lean kernel, no solver, no native decision, and only standard axioms. An independent digit dynamic program also recovered the exact minimum.

## Replay

Use Lean 4.34.1 and built Mathlib at d13f23b723b8a846827a245b89c10fc7d3f11612.
From this directory, decode and unpack the bundle with `base64 -d certificate.tar.gz.base64 | tar -xz`.
Then run `MATHLIB_DIR=/path/to/mathlib LEAN_BIN=/path/to/lean bash src/replay.sh`.
`python3 src/audit.py` independently checks the minimum and both products.
The bundled C064Core uses a minimal-import verbatim excerpt of the original arithmetic lemmas.
