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

### V11: common quantitative bounds

The actual iid pattern probabilities have the required power-law bounds
at a single scale d=ceil(log N/X). A common cutoff works simultaneously
for the triangle, diamond, forbidden pattern and charged attachment.
The four second-moment and deletion ratios decay as N^(-eta) for one
positive eta. `GeometricQuantitativeAssembly.concrete_moment_error`
bounds the total non-spectral error by 1/2 for all sufficiently large N.

`GeometricMomentEvents.labeled_moment_probability` connects any fixed
injective labeling to the finite spherical graph law. Particular indicator
bridges for charge and triangle overlap, and the cap-link expansion input,
remain to be assembled in Lean.

### V12: complete conditional reduction

All joint triangle moments and charged deletion indicators are now
verified against the actual finite spherical graph law. Distinct
triangles sharing at most one vertex factor exactly, and two sharing
an edge give the diamond probability.

`GeometricFolkmanReduction.folkman_given_cap_margin` derives the full
finite graph conclusion from one explicit remaining hypothesis:
at the chosen spherical density, the sample has a fixed positive
monochromatic-triangle margin for every two-edge-coloring with
probability at least 1/2 along arbitrarily large sample sizes.
This is a parameterized theorem, not a Lean axiom or an unconditional
verification. The cap/link spectral justification is still paper-only.

### V13: exact spectral interface

The actual link edge set is verified to be the induced graph on
neighbors of the root. Its ordered adjacency sums count each link edge
and each cut edge twice. The normalized lower spectrum, including the
zero-degree convention, gives the link MaxCut fraction and hence the
global coloring margin by exact corner counting.

`GeometricSpectralInterface.folkman_given_bottom_link_failure` reduces
the remaining hypothesis to a lower spectral bound of -1/4 in every
link, with failure probability at most 1/2. No upper spectral gap is
needed. The finite-product restriction identity and root-independent
positive cap mass are kernel checked. The actual high-probability
lower spectral estimate is still outside Lean.

### V14: a typical link suffices

The exact finite-measure conditioning law shows that, conditional on
the retained indices, their labels are independent with the normalized
cap measure. The number of retained labels has the binomial law.

The weighted corner count permits exceptional links, charged by their
edge counts rather than by their number. Rooted triangle indicator
moments give a uniform second-moment bound at the correct scale; the
triangle and diamond rates make the relative rooted variance tend to
zero. The global triangle count concentrates at the same dimension.

`GeometricTypicalFolkman.folkman_given_typical_root_cuts` now gives the
final graph from just one remaining input: the chance that a uniformly
random root has a cut crossing more than five eighths of its link edges
is at most 1/82944 along arbitrarily large samples. There is no
longer a simultaneous expansion or inverse-polynomial-tail requirement.
The analytic bound for a random rooted link is not yet proved in Lean.

### V15: explicit shell loss for the actual sphere law

The three-edge Gram density now yields an explicit exponential bound
on triangle mass discarded by trimming either of the two edges at a
root. With density exponent m/2, root threshold t, and shell width
A/((m/2)t), the lost triangle mass is at most 2 exp(36−A) times the
total triangle mass for all sufficiently large m. There is no appeal to
a limiting asymptotic. The proof uses a determinant supporting plane,
a lower corner box, and exact elementary exponential integrals.

For heights in the retained shell of width w≤t, the residual threshold
lies between t/(1+t)−4tw and t/(1+t). An exact deterministic estimate
transfers a 9/16-cut bound from a subgraph keeping at least 6/7 of the
link edges to the required 5/8 bound. The count and spectrum of the
residual spherical graph still require probabilistic analysis. The
final Folkman theorem remains conditional.

### V16: exact conditioning at a fixed root

An orthogonal height coordinate is independent of the residual
direction on the sphere. Given the exact set of sample labels in
a measurable height band of positive mass, the remaining directions
are therefore iid uniform on the tangent sphere. The split isometry
works for any root. Edges between retained labels obey the two
residual threshold brackets. The triangle shell-loss probability
bound also holds for each fixed root, not just a random root.

For the remaining sample concentration step, the mean of the
cross-block matrices over uniform binary splits is exactly half the
original zero-diagonal matrix. The random-matrix bound relating the
tangent sphere sample to its population kernel is not yet formalized.

### V17: residual density and cut interfaces

The rank-one split gives the exact finite-dimensional height density.
A shell of the chosen width contains a constant fraction of the
full cap. The gap between the tighter and looser residual thresholds
has arbitrarily small relative edge mass, with a single positive
threshold chosen independently of sample size. The expected residual
degree scale is polynomial in the host size, including the
one-dimension drop from the host to the tangent sphere.

The cross-partition average bounds any linear-image norm of a
zero-diagonal matrix. A lower centered-quadratic bound at scale
one tenth of the expected degree supplies both the tighter graph's
edge-count lower bound and its required 9/16 cut bound. This does
not yet verify the random-matrix estimate itself.

### V18: population Lipschitz contraction and finite covariance

Two reflections give a measure-preserving rotation between the caps at
any two roots. Lean checks the exact planar displacement, the tangent
second moment bound, the conditional height-squared bound, and the
resulting dimension-explicit Lipschitz contraction of cap averaging.
This is not yet a spectral bound on L². The abstract self-adjoint
power argument is verified separately.

The finite rank-one covariance variance bound, norm equality for the
two empirical Gram matrices, and covariance monotonicity under column
truncation are checked. A measurable Euclidean grid supplies the
quantization geometry. The fixed-root shell loss has a checked
finite-sample Markov bound. The proof connecting these ingredients to
the required spherical sample cut estimate remains incomplete.

### V19: population L² contraction

The exact spherical cap kernel is symmetric and stationary. A
dimension-explicit bound on the measure of a strip implies that cap
averaging takes every bounded measurable test to a Lipschitz test.
The self-adjoint power argument then bounds the L² norm on centered
Lipschitz tests, and a smoothing step plus Cauchy--Schwarz removes
the Lipschitz restriction.

`GeometricPopulationL2.cap_l2_contraction_bounded` covers all
bounded measurable centered tests, including the lifted finite-grid
vectors. The next step is the finite-grid population matrix comparison
and the concentration of the actual spherical sample. The graph
conclusion remains conditional.

### Finite-grid population bound

`GeometricQuantizedCap.quantized_centered_cap_operator` bounds the norm
of the centered weighted kernel on the explicit measurable coordinate
grid. It includes cells of zero mass. A difference between the spherical
and grid adjacency tests is supported on a strip whose mass is bounded
by the one-coordinate density, and the operator pays its square root.
This is a population operator, not a bound for the random sample. The
random sample concentration and the final graph conclusion are not yet
verified in Lean.

### Sample quantization error and finite-kernel inputs

`GeometricSampleQuantization.sample_cap_quantization_tail` controls
the empirical operator error between actual and grid-quantized
adjacency. Its sparse strip-degree estimate conditions on each sample
row and does not assume different rows are independent.
`GeometricGridResolution` bounds both this strip probability and the
logarithm of the grid size. `GeometricGridRowMass` and
`GeometricKernelBernoulli` supply explicit row and column energy bounds.
The centered quantized sample itself still needs a concentration
argument; these lemmas do not assert the finite graph conclusion.

### Finite sampling, with the optional concentration dependency

The native modules verify the exact iid grid law, the squared column
truncation estimate, and averaging over all splits without a union over
splits. The optional `GeometricActualSampleNorm.spherical_actual_sample_tail`
then gives an explicit probability bound for the centered adjacency
of independently sampled points on the actual sphere, not only the grid.
This is not the graph existence theorem: the atypical cut bound still
requires assembling the shell probabilities and graph-level transfer.

The optional proofs use the established matrix Bernstein theorem
`RMT.matrix_bernstein_inequality_hdp_all` of
[Yuanhe Zhang, Jason D. Lee and Fanghui Liu's SLT project](https://github.com/YuanheZ/lean-stat-learning-theory/tree/482a1a56daf792b33afe8cf7f07f127dc0af8640).
That theorem is reused, not an original contribution. The accompanying
compatibility patch modifies three upstream files for Mathlib 4.34.1;
the upstream files retain their original copyright and Apache-2.0 notices.
See `SLT-LICENSE.txt`. With a local checkout of exact upstream commit
`482a1a56daf792b33afe8cf7f07f127dc0af8640`, set `SLT_V432_DIR` to that
checkout directory when running `bash replay.sh`. The replay checks hashes,
copies and patches only five specified Lean files into a temporary directory,
and uses the pinned Lean compiler directly. It does not run an upstream
build script or modify the caller's checkout. With the variable unset the
ordinary native replay works without SLT.
