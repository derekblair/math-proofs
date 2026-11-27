# Predetermined separator normals do not improve radial stochastic clipping

This is a negative result for a restricted stochastic model, not for lattice-adaptive normals or the Euclidean chromatic number. The radial rule is exactly optimal in the unrestricted Poisson-center model, and no predetermined direction-only rule improves the leading exponential density for Haar lattices. The result allows tilts arbitrarily close to tangency and, as shown below, simultaneous deterministic odd offsets.

Fix dimension d≥2, seed radius R>0, and A≥2R. Fix in advance any Borel odd map n from the unit sphere to itself with a(u)=n(u)·u>0 everywhere. For center displacement su (s>0), retain offset x in the open ball B_R only when x·n(u)<(s a(u)−A)/2. Radial clipping is n(u)=u. This gives between-cell separation greater than A because the rule at the opposite center uses n(−u)=−n(u). With A=1+ε and 2R=1−ε, all translates are separated across the forbidden band. Tilted cutoff is (A+2R)/a0 only if a(u)≥a0>0 uniformly: do not reuse the radial distance-two cutoff for arbitrary tilts. With no angle lower bound, some distant vectors can cut. The cells remain Borel (countable intersections) but openness is not needed.

## Geometric comparison

Let σ be normalized spherical measure and v_d unit-ball volume. The displacement volume that removes x is
F_n(x)=v_d ∫[(A+2x·n(u))/a(u)]^d dσ(u).
For an origin-symmetric center process (a lattice) the void event is equivalently emptiness in an antipodal representative of F_x∪(−F_x). Its volume is
H_n(x)=(v_d/2) ∫[(A+2|x·n(u)|)/a(u)]^d dσ(u).
Both are even convex functions of x on B_R, simultaneously finite or infinite in the interior according as ∫a^(−d) is finite or infinite. The latter case gives zero void probability for Poisson immediately and for Haar lattices by bounded truncation and the Rogers estimate below.

For either volume function G, define E={x∈B_R:G_n(x)<t}. If its volume is positive, replace by its convex closure without changing volume or integrals. Write B_ρ for the equal-volume ball. With X uniform on E, take D_E to be the convex body whose support function is ||A||y||+2X·y||_{L_d} for F, or ||A||y||+2|X·y|||_{L_d} for H. The displayed pointwise terms are nonnegative convex functions of y, so Minkowski's inequality gives a support function; D_E contains A B by symmetry and Jensen. Integrating over x and using h_{D_E}(n(u))/a(u)≥ρ_{D_E}(u) yields (1/|E|)∫_E G_n≥vol(D_E) for F and ≥vol(D_E)/2 for H. For radial n(u)=u and E a ball these are exact equalities.

Steiner symmetrization decreases vol(D_E). For clarity, the support-function dual representation of D_E is the closure of the points
2 ∫ f(x) b(x) x dμ_E(x) + A(∫ f dμ_E)w,
where f≥0, ||f||_{d/(d−1)}≤1, ||w||≤1; b≡1 for F and |b|≤1 for H. This follows by Hölder duality and choosing w and b to maximize the directional objective. In a vertical fiber of E with midpoint c(x'), the two measure-preserving maps from the centered Steiner fiber are s↦c(x')+s and s↦c(x')−s. Transfer f and b along both and reflect the vertical coordinate of w in the second. A point of D_{Steiner E} then gives two points of D_E with the same horizontal coordinate and vertical difference twice the original point's vertical coordinate. This proves D_{Steiner E}⊆Steiner(D_E). Successive symmetrizations can tend to B_ρ; continuity of the normalized support integrals under convex-body convergence finishes vol(D_E)≥vol(D_{B_ρ}). One self-contained route to convergence is taking at each step a direction that nearly maximizes the decrease of ∫|x|²; this drop equals the fiber integral of length times the squared midpoint. In a convex Hausdorff limit the drop in each fixed direction is continuous, and any subsequential limit must have zero drop for all directions, hence be the centered ball.

Thus ∫_E G_n≥∫_{B_ρ}G_rad. Since radial G_rad is nondecreasing in |x|, the exact stop-loss bound follows:
∫_{B_R}(t−G_n)_+=∫_E(t−G_n)≤∫_{B_ρ}(t−G_rad)≤∫_{B_R}(t−G_rad)_+.
By representing a nonnegative decreasing convex function vanishing at infinity as a positive combination of these hinges, it follows that ∫φ(G_n)≤∫φ(G_rad). In particular this works for exp(−λz) and 1/z (bounded away from zero here).

## Stochastic consequences and scope

For a homogeneous Poisson process on unprojected R^d of intensity I, Slivnyak–Mecke and the disjoint cells give exact expected retained fraction I∫_{B_R}exp(−I F_n)dx. Radial normals maximize this at every intensity and dimension covered by the argument. No torus projection or finite-angle hypothesis is needed. Periodic iid finite-center variants retain the exponent if the tilt is uniformly bounded away from tangency: the forbidden volume then lies in a ball of constant radius, so projection modulo 2Z^d loses at most a polynomial multiplicity as in the earlier Davies audit.

For Haar lattices of covolume V, Rogers' second moment bounds the probability of missing a set of positive volume H by min(1,CV/H) for absolute C in d≥3. The correction integral for the indicator is bounded by H/max(|p|,q)^d over coprime q≥1 and p≠0, and the sum of these reciprocals is bounded uniformly d≥3 by summing O(m) pairs with max(|p|,q)=m. For unbounded sets, apply the bound to finite bounded subsets and enlarge by truncations. Therefore E[density]≤C∫1/H_n≤C∫1/H_rad. At R=(1−ε)/2 and A=1+ε this is O((R/g(R))^d), because H_rad≥F_rad/2, F_rad(x)≍v_d g(|x|)^d by the audited saddle estimate, and d/dlog r log(r/g(r)) is bounded below. At ε→0 the unit-distance base in reciprocal density is 3√3/2, uniformly over all covolumes and such predetermined normal maps.

At the natural scale F_rad(R)/V=Θ(1), use Klartag's TV theorem on the antipodal-free representative. Its void error is uniformly exponentially small even if the normalized representative volume exceeds cd: pass to a measurable subset of volume cd/2 to bound the whole void probability; the Poisson void probability itself is also exponentially small. Thus at this scale exact geometric optimization for φ(z)=exp(−z/V) shows no improvement over the sharp radial prefactor c_* within these deterministic normal maps. The error is additive on probability and is not asserted to control the sharp constant at completely arbitrary V. The all-V leading exponential obstruction uses Rogers instead.

Not covered: normals depending on the sampled full lattice or point configuration; normals depending on displacement radius; dependent non-Haar center laws; replacing the seed ball by a different body; exceptional deterministic choices. No new exponential coloring improvement found here. A coded product with hard minimum Hamming distance loses because it must allocate gap ≥1/√L to active blocks and pays code covolume redundancy, before any potential soft-distance refinement.

## Literature check

Davies §10, https://arxiv.org/html/2610.12301v1#S10, uses radial normal cuts in the periodic iid setting. The Steiner method is related to the classical L_p Busemann–Petty centroid inequality (Campi and Gronchi, https://doi.org/10.1006/aima.2001.2036, following Lutwak–Yang–Zhang), and later Orlicz–Lorentz versions, https://doi.org/10.1186/s13660-019-1962-5. The absolute-value auxiliary body with A=0 is the usual L_p centroid body up to constants; the proof here retains the Euclidean A||y|| term inside the moment and derives a blocker-volume distribution comparison, rather than claiming the centroid inequality is new. No directly matching clipping/Poisson theorem surfaced; no priority claim. Random lattice inputs are Rogers, https://doi.org/10.1007/BF02392493, and Klartag Theorem 1.2, https://arxiv.org/html/2605.10479v1#Thmtheorem1.2.

## Joint fixed tilt and odd displacement offset

The same stop-loss comparison extends to adding any fixed measurable odd scalar offset h(u) to the cut, with normal n as above, for which the blocking volumes are defined (for instance bounded h). Scale h by an auxiliary real parameter b. The Poisson blocker integrand has numerator (A+2(x·n(u)−b h(u)))_+^d before dividing by a(u)^d; the Haar antipodal numerator is (A+2|x·n(u)−b h(u)|)^d. The resulting volume G_b(x) is jointly convex in (x,b), with G_{−b}(−x)=G_b(x). For each t, the nonnegative function (t−G_b(x))_+ supported on B_R is log-concave in (x,b), being a positive concave function on its convex positive support and zero elsewhere. Prékopa gives an even log-concave x-integral, hence it is maximal at b=0. Combine with the fixed-tilt comparison. Also, choosing from a predetermined exp(o(d))-size menu after observing the lattice preserves the leading ceiling by summing expected densities; unbounded adaptive selection is not covered.
## Simultaneous odd offsets and tilts

Let the cut be \(x\cdot n(u)<(s a(u)-A)/2+h(u)\), where \(h\) is any
predetermined Borel odd scalar function of direction, for example a
bounded one. The reverse cut cancels the offset, preserving the same
strict gap. The ordinary forbidden radial function is now
\((A+2(x\cdot n(u)-h(u)))_+/a(u)\); the antipodal representative
uses \((A+2|x\cdot n(u)-h(u)|)/a(u)\), with the same \(v_d/2\) factor.

Replace \(h\) by \(sh\), with real interpolation parameter \(s\).
The corresponding volume \(G_s(x)\) is a jointly convex extended
function of \((x,s)\), by the displayed positive-part or absolute-value
formulas, and \(G_{-s}(-x)=G_s(x)\). At each threshold \(t\), the function
\(\mathbf1_{B_R}(x)(t-G_s(x))_+\) is log-concave: its positive support
is convex and it is concave on that support. Its integral over \(x\)
is even and log-concave by Prékopa, so is greatest at zero. Thus the
stop-loss comparison first removes the offset and then removes the
tilt. The exact Poisson optimum and Haar exponential obstruction
hold for simultaneous deterministic odd tilts and offsets. This does
not assert the same result for interacting point-process marks or
arbitrary lattice-dependent offsets.

For the uniform asymptotic integral in this note, \(g(r)\) is the maximum
of \((A+2rt)\sqrt{1-t^2}\) for \(0\le t\le1\). For the unit-distance
margin \(A=1+\varepsilon,\ R=(1-\varepsilon)/2\), the angular saddle
stays uniformly in \([0,1/2]\) for \(0\le r\le R\).
Integrating over an interval of width proportional to \(d^{-1/2}\)
about the saddle yields \(F_{\rm rad}(r)\ge c_0 v_d g(r)^d\) uniformly,
using bounded log curvature and the spherical normalizer of order
\(\sqrt d\). At \(r>0\), \(d\log g/d\log r=2rt/(A+2rt)\le 1/3\)
since \(2r\le A\) and \(t\le1/2\). Thus the integral of
\(v_d^{-1}g(r)^{-d}\) over the ball is at most
\((3/2)(R/g(R))^d\) by volume-radius substitution. The constants in
the Haar exponential estimate do not depend on the chosen tilt map.

## Why adaptation remains an open route

For a deterministic planar lattice generated by \((L,0)\) and
\(L(c,s)\) with \(L=8/5,\ (c,s)=(20/101,99/101)\), only the basis
vectors and their negatives have length below 2. At \(R=1/2,A=1\),
the radial cell is a full parallelogram inside the seed disk. With
two active normals forming an acute angle, rotate them inward by
the angle with cosine \(9999/10001\) and sine \(200/10001\);
keep the other displacement normals radial. The two strip widths
decrease only quadratically, while the angle between them decreases
linearly. The resulting parallelogram remains within the seed disk
and has exact area \(90821237069/245351702475\), larger than the
radial \(101/275\). This witnesses the limitation of extending the
expectation comparison to individual lattices; it does not yield
any high-dimensional improvement.

Lowering the forbidden volume by optimizing each offset separately
also does not give a cell. On the lattice with basis \((11/10,0),(0,3)\),
the two offsets \((1/20,2/5)\) and \((-1/20,2/5)\) each have their own
pointwise-safe symmetric segment, but their differences across one
translate realize distance exactly 1. Both examples are checked by
python3 tilt-replay.py using exact rational inequalities.

Lean file StopLoss.lean checks a finite stop-loss implication and
the nonnegative mixture step. It does not formalize the measure
theory, Steiner symmetrization, Poisson or random-lattice results.
For Mecke see [Last–Penrose, Chapter 4](https://stoch.math.kit.edu/297.php).
The shift comparison uses the classical Prékopa marginal theorem,
not a new version of log-concavity. Related project results:
[sharp iid radial density](https://github.com/derekblair/math-proofs/pull/119)
and [one-cell radial construction](https://github.com/derekblair/math-proofs/pull/123).
