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
- The determinant maximizer exists over the real feasible Gram set. For symmetric constraints on at most six vertices and 0 < t ≤ 1/20000, Lean verifies that every constrained off-diagonal entry equals t and every free one has magnitude below t/2. This includes compactness, the determinant lower probe, principal determinant comparison, and feasible Schur perturbations.
- Lean verifies the exact determinant multiplier for attaching a page to a saturated edge, and that the actual constrained subdivided-K4 maximum is strictly smaller than the three-page book determinant. GeometricExactScalar.lean checks the scalar consequences. [EXACT-RATE.md](EXACT-RATE.md) integrates the determinant calculations into the written rate argument.
- Lean checks the exact log rates for all five actual Gram pattern maxima and the full strict dimension window, including the cap-rate identity.
- The normalized Haar sphere product gives a finite probability law for the threshold graph. Lean checks that each prescribed labeled graph event is its Gram event under the corresponding iid marginal. Orthogonal reorientation preserves the spherical probability, and the two-point rooted triangle probability is independent of the fixed root.
- The joint Gram density, its rare-event and shared-root moment bounds, and the link spectral theorem needed to supply the finite-distribution inputs remain unformalized.

## Reproduce

Use Lean 4.34.1 and built Mathlib at d13f23b723b8a846827a245b89c10fc7d3f11612.
Run MATHLIB_DIR=/path/to/mathlib LEAN_BIN=/path/to/lean bash replay.sh.
The checked declarations use only Lean's standard axioms.

### V7: determinant-integral rates

The shared-root triangle factorization is now proved for actual independent
Haar sphere points. The correlation chart uses one real coordinate per
unordered off-diagonal pair. The feasible set is compact in this chart; every
strictly submaximal determinant level contains a nonempty open subset of the
feasible region and therefore has positive Lebesgue volume. The unconditioned
determinant maximum is exactly one.

`GeometricNormalizedRate.normalized_determinant_log_rate` proves that the log
of the normalized determinant-power integral, divided by its real power,
approximates the log of the feasible maximum to any prescribed error beyond a
finite cutoff. It tracks positivity and finiteness of both integrals. This
does not identify that integral ratio with the spherical Gram distribution.
The distribution identity and the cap link spectral input remain outside Lean.

### V8: orthogonal projections of spherical samples

The normalized Haar unit sphere in an orthogonal sum of a k-dimensional
coordinate space and an (m+2)-dimensional residual space has an exact
projection law. For any nonnegative measurable weight of the first k
coordinates, its spherical expectation is the ratio of the corresponding
weighted and unweighted Lebesgue integrals on the open unit ball, with
density proportional to (sqrt(1 - sum x_i^2))^m.

The proof checks the actual Fréchet derivative, the split-polar Jacobian
and its domain bijection, Lebesgue change of variables, exact Haar polar
disintegration and positive finite normalizer cancellation. The main
interface is `GeometricProjectionLaw.spherical_projection_probability`.
The varying-span nonorthogonal pushforward and the full joint spherical
Gram law still need Lean proofs. The cap-link spectral input is unchanged.

### V9: conditional Gram law with fixed anchors

For any fixed independent anchor tuple the exact law of the inner products
of an independent spherical sample with the anchors depends only on their
Gram matrix. The proof transfers spherical probability by a linear
isometry, projects onto the span, and changes from orthonormal coordinates
to anchor inner products with inverse Jacobian 1/sqrt(det Gram).
`GeometricFixedAnchors.sphere_fixed_anchor_conditional` states the resulting
ellipsoid integral. The determinant power telescopes through the Schur
complement. Finite iid sphere tuples are almost surely linearly independent
up to ambient dimension, and the proof explicitly discards only null
lower-dimensional spans.

The joint Gram law still needs recursive chart bookkeeping and the
measure-level Fubini induction. The cap-link spectral input is unchanged.

### V10: completed joint Gram density and actual pattern rates

`GeometricJointGram.spherical_joint_gram_weighted` proves the exact joint
off-diagonal Gram density of n independent normalized Haar sphere points
in dimension n+m+1. It applies to every nonnegative measurable weight.
`GeometricJointGramNormalized.spherical_joint_gram_normalized` normalizes
the density exactly. In the positive-power case, singular positive
semidefinite matrices contribute zero; this requires no boundary-null
assumption.

`GeometricSpherePatternRate.sphere_pattern_mass_integrals` connects the
density to the actual prescribed threshold-pattern event, and
`GeometricActualRate.sphere_pattern_rate_exp` proves its two-sided
exponential rate (for n at most six and sufficiently small positive
threshold). This closes the spherical Gram law and determinant-rate
inputs in Lean. The cap-link spectral theorem and the final asymptotic
probability assembly are not yet formalized.
