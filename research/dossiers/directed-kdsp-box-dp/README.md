# Directed k-disjoint shortest paths with a quadratic parameter exponent

[The proof and algorithm](BOX-DP.md) give a deterministic n^{O(k²)}
algorithm in the Cao–Qi–Wang exact comparison/addition model for arbitrary
directed graphs with strictly positive real weights. This resolves the
polynomial-in-k exponent part of [Question 11.1](https://arxiv.org/html/2611.34013v1#S11).
The linear-in-k exponent and Question 11.2 on sweep width are not settled.

[Independent review](AUDIT.md) checks both the geometry and the composition
argument. The exact-rational geometry and small-integer graph checkers do not
replace the general proof. The latter is a differential test against enumerated
path witnesses, not an optimized implementation.

## Replay

Run `python3 geometry_check.py` and `python3 box_dp_check.py` here.
Run `lake env lean /absolute/path/to/BoxProgress.lean` from a built Mathlib
v4.34.1 checkout (commit d13f23b723b8a846827a245b89c10fc7d3f11612).
The Lean file checks key projection inequalities and the tied-position
common progress claim, not the full algorithm. [Replay output](REPLAY.txt)
records the checked lemmas and their axiom dependencies.
Run the same command on `BoxCore.lean` to check the finite averaging, telescoping, and face-count lemmas.
