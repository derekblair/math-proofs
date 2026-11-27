# The subdivided-K4 edge Folkman question

[Hassan, Radziszowski and Van Overberghe, Problem 1](https://arxiv.org/html/2605.16542v1#S6) asks for a finite graph that avoids the graph obtained by subdividing one edge of K4, but has a monochromatic triangle in every two-coloring of its edges.

[PROOF.md](PROOF.md) gives a written affirmative proof draft. It uses a positively correlated spherical random graph and deletes one selected edge from every forbidden copy. The sphere makes triangles plentiful enough for a uniform coloring margin but makes the forbidden configuration plus an attached triangle too rare to erase that margin. An independent mathematical review found no gap in the written argument. This is a draft, not an end-to-end Lean proof, a numerical witness, or a priority claim.

- RobustFolkman.lean checks the finite preservation argument and exact charge for removing edges.
- MixedCorners.lean checks the normalized count of monochromatic triangles from a mixed-wedge bound.
- ParagliderCayley.lean is a separate, fully checked restriction: any group with an inverse-closed and conjugacy-invariant connection set has triangle codegree at most two if its Cayley graph avoids the subdivided K4. This does not restrict the random geometric construction.
- The spherical spectral theorem, Gram-rate asymptotics, and the final probability and existence step are not formalized here.

## Reproduce

Use Lean 4.34.1 and built Mathlib at d13f23b723b8a846827a245b89c10fc7d3f11612.
Run MATHLIB_DIR=/path/to/mathlib LEAN_BIN=/path/to/lean bash replay.sh.
The checked declarations use only Lean's standard axioms.
