# The subdivided-K4 edge Folkman question

[Hassan, Radziszowski and Van Overberghe, Problem 1](https://arxiv.org/html/2605.16542v1#S6) asks for a finite graph that avoids the graph obtained by subdividing one edge of K4, but has a monochromatic triangle in every two-coloring of its edges.

[PROOF.md](PROOF.md) gives a written affirmative proof draft. It uses a positively correlated spherical random graph and deletes one selected edge from every forbidden copy. The sphere makes triangles plentiful enough for a uniform coloring margin but makes the forbidden configuration plus an attached triangle too rare to erase that margin. An independent mathematical review found no gap in the written argument. This is a draft, not an end-to-end Lean proof, a numerical witness, or a priority claim.

- RobustFolkman.lean checks the finite preservation argument and exact charge for removing edges.
- MixedCorners.lean checks the normalized count of monochromatic triangles from a mixed-wedge bound.
- ParagliderCayley.lean is a separate, fully checked restriction: any group with an inverse-closed and conjugacy-invariant connection set has triangle codegree at most two if its Cayley graph avoids the subdivided K4. This does not restrict the random geometric construction.
- GeometricGraphEdit.lean and GeometricAssembly.lean verify the exact graph statement from quantitative finite-distribution inputs: spectral exception mass, triangle variance, and expected deletion charge. GeometricMoment.lean proves the finite selection step with those inputs.
- GeometricPatterns.lean checks the five pattern sizes, and GeometricWindow.lean checks the parameter inequalities under fourth-order remainder bounds.
- GramLowOrder.lean and GramCoefficients.lean verify the determinant coefficients through cubic order for a symmetric Boolean adjacency, with arbitrary nonedge entries at quadratic scale. Those terms are 1, 0, minus the edge count, and twice the triangle count.
- GeometricVariance.lean and GeometricTriangleOverlap.lean check the variance bound for triangle-indicator events from individual and pair probabilities. For each triangle there are at most 3(n−3) distinct triples sharing two vertices. GeometricConditioning.lean checks an exact finite product-conditioning identity for constant conditional probabilities.
- GeometricChargeMoment.lean checks the finite expectation bound from a pointwise internal and fresh certificate majorant. The random spherical certificate probabilities are a separate input.
- GeometricChargeGraph.lean and GeometricChargeCount.lean use the actual forbidden copies and their attached triangles. They bound the expected loss by 3 n^5 p_H + n^6 p_J. GeometricTriangleCount.lean connects the unordered triple indicators to the actual graph triangles. GeometricPatternAssembly.lean combines these bounds into the exact graph conclusion from the point and pair probabilities, the spectral coloring margin, and one explicit inequality.
- GeometricGap.lean and GeometricHGram.lean check an alternative exact determinant comparison for a symmetric five-vertex Gram matrix whose seven constrained entries already equal the threshold. These lemmas do not prove that an optimizer has these properties.
- GeometricAttachment.lean proves the sharp quadratic minimum when imposing two positive correlation lower bounds in a positive semidefinite bilinear form. The matrix determinant transfer by Schur complement and the optimizer saturation argument are separate.
- The spherical law, its rare-event estimates, and the spectral theorem needed to supply the finite-distribution inputs are not formalized here.

## Reproduce

Use Lean 4.34.1 and built Mathlib at d13f23b723b8a846827a245b89c10fc7d3f11612.
Run MATHLIB_DIR=/path/to/mathlib LEAN_BIN=/path/to/lean bash replay.sh.
The checked declarations use only Lean's standard axioms.
