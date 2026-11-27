# Sparse lattice-adaptive cuts cannot improve the sharp radial density

Sample a Haar lattice in Euclidean dimension d at arbitrary deterministic covolume V. Use the Davies radial cuts with open seed radius R=(1−ε)/2 and gap A=1+ε, where ε≥0 tends to zero. A nonzero displacement su excludes offsets x with x·u≥(s−A)/2. Fix M_d≤exp(17d/1000). A measurable rule may inspect the whole lattice and replace the cuts for at most M_d antipodal pairs of its displacement vectors, keeping all other cuts. No spacing or angular restriction is imposed on those replacements for the upper bound. In the density model the resulting seed piece is translated by the lattice and the choices must still produce a valid separated construction. Write B_d for the supremum over V of expected radial seed volume divided by V. Then, uniformly over V and allowable adaptive choices, the expected modified seed volume divided by V is at most B_d+o((R/g(R))^d), with
$$
g(r)=\max_{0\le t\le1}(A+2rt)\sqrt{1-t^2}.
$$
Since B_d is bounded above and below by positive constants times (R/g(R))^d, the supremum in the larger class is (1+o(1))B_d. Separately, the same conclusion holds for Borel direction-only predetermined tilts and odd direction offsets from the [stop-loss comparison](https://github.com/derekblair/math-proofs/pull/124), without a sparsity restriction. These are expected density results for restricted models, not obstructions to arbitrary adaptive cuts or Euclidean colorings.

## Geometry and normalization

For offset x of radius r let F_x be the radial blocker in displacement space, and H_x half the volume of F_x∪(−F_x). Thus H_x counts volume in an antipodal representative, and H_x lies between |F_x|/2 and |F_x|. Uniformly in r, |F_x| is comparable with v_d g(r)^d, where v_d is unit-ball volume. Indeed radial integration over displacement lengths gives v_d times the spherical average of (A+2rt)^d. The spherical coordinate t has density proportional to (1−t²)^((d−3)/2). Use the saddle of (A+2rt)√(1−t²), with maximizer t*∈[0,1/2] and nondegenerate uniform log curvature. The window of width d^(−1/2) cancels the order √d of the density normalizer. Fixed endpoint intervals have exponential loss, obtained by integrating there with the full spherical density.

By stationarity, d log g/d log r=2rt*/(A+2rt*)≤1/3. Normalize with λ=v_d g(R)^d/V and the uniform radial-volume coordinate u=(r/R)^d. Then H_x/V≥c λ u^(1/3) for absolute c>0 and the unit-distance parameter regime. Density divided by (R/g(R))^d is λ times the seed-average retention probability. At λ=1 the uniform random-lattice Poisson approximation below gives a positive lower bound for the normalized radial density.

## Fourth moment for every intensity

Let S be a bounded symmetric Borel set in displacement space on a Haar unimodular lattice, with volume v≥1, and X the number of nonzero lattice points in S counting both signs. From [Strömbergsson and Södergren](https://arxiv.org/html/1611.06332), equations (3.2)–(3.6), the main terms of E(X−v)^4 are 12v²+8v, and its nonnegative remainder is a sum of terms with ranks 1, 2 or 3. Apply the estimate (3.6) at volume d, so the remainder is O((3/4)^(d/2)d³) uniformly for large d. Homothetically rescaling the test set from volume d to v multiplies each rank-m term by (v/d)^m: change variables in its m displacement integrals. Thus for v≥d use (v/d)^3 to bound every term and for 1≤v<d use 1 and absorb the d³ into the exponential. In particular E(X−v)^4≤C(v²+e^(−cd)v³). Bounded symmetric truncations handle finite-volume unbounded sets by monotone convergence for the counts and Fatou for the fourth moment. All volume parameters for covolume V are divided by V.

A survivor after M edits has X≤2M, with mean v=2H_x/V for the original symmetric blocker. At v>4(M+1) the fourth moment bounds this event by C(v^(−2)+e^(−cd)/v). The set of radial u where the bound cannot be applied has measure at most min(1,C((M+1)/λ)^3). Integrating the other terms using u^(−2/3) and u^(−1/3) yields the all-V normalized upper bound
$$
C\big(\lambda^{-1}+e^{-cd}+(M+1)^3/\lambda^2\big).
$$
In particular edited density is negligible when λ≥exp(δd), where δ=511/20000 and 3·17/1000<2δ. With M=0 this also bounds the large-λ tail of the radial model, and λ itself bounds the small-λ tail.

## Averaging the caps for smaller intensities

Any point recovered relative to the original seed was cut by at least one edited vector pair. For one vector of length s>A the removed seed fraction is at most the fraction in a pair of opposite caps at height (s−A)/2. It is at most poly(d)(1−((s−A)/(2R))²)^((d−1)/2) when s<A+2R, and zero when s≥A+2R, by integrating the coordinate density in the ball. Use the trivial bound 1 for s≤A. Take a=161/125. Bound the recovery fraction by the sum of all such cap fractions for nonzero vectors of length at most a plus M times the cap bound at a. This inequality is pointwise in the entire lattice, regardless of how edits were selected.

By Siegel's mean-value formula the short-vector sum has expectation at most (d v_d/V) times the integral of s^(d−1) times the cap fraction over [0,a]; counting both signs merely overcounts. For s∈[A,a], s√(1−((s−A)/(2R))²) is increasing, since (2R)²>(s−A)(2s−A) uniformly for sufficiently small ε. Its value at a exceeds A, so the portion s≤A has no larger exponential base. At ε→0 put g_*=3√3/4,
$$
\eta=\log\frac{g_*}{a\sqrt{1-(a-1)^2}},\qquad
\gamma=-\frac12\log(1-(a-1)^2).
$$
Multiplying by λ for density normalization gives total gain bounded by
$$
\operatorname{poly}(d)\big(\lambda^2 e^{-(\eta+o(1))d}
       +\lambda M e^{-(\gamma+o(1))d}\big).
$$
Here 2δ<η and δ+17/1000<γ. To see both with rational arithmetic, put x=(a−1)² and q=27/[16a²(1−x)]−1. Use γ≥x/2+x²/4 and η≥(q−q²/2)/2, via integration of 1/(1−x) and 1/(1+q), respectively. This gain tends to zero uniformly for λ≤exp(δd), giving the claimed adaptive ceiling.

## Arbitrary-covolume upgrade for predetermined directions

For a predetermined direction tilt and simultaneous odd offset, let H(x) be the volume of its antipodal representative. The [fixed-direction stop-loss result](https://github.com/derekblair/math-proofs/pull/124) gives ∫φ(H(x))dx≤∫φ(H_x)dx for every nonnegative decreasing convex φ vanishing at infinity, including inverse first and second powers and exp(−z/V). For the event that H's representative is empty the fourth-moment bound is C[(V/H)²+e^(−cd)V/H], trivial with large enough C when H<V. Infinite-volume misses have probability zero by bounded truncation. Applying the stop-loss order to the two inverse moments gives the same O(λ^(−1)+e^(−cd)) normalized density bound uniformly for λ→∞. Again λ→0 is trivial.

For bounded λ use [Klartag, Theorem 1.2](https://arxiv.org/html/2605.10479v1#Thmtheorem1.2) on the measurable antipodal representatives of the blockers, which are disjoint from their own negatives. It approximates their void probabilities by e^(−H/V), with additive exponentially small error uniformly even when H/V is large. For excessive volumes take a measurable subset of normalized volume proportional to d and bound the whole void probability by its exponentially small void probability. The radial model has the same approximation at bounded λ, with H replaced by H_x. The exponential convex comparison compares the approximating integrals at the same V. After normalization its uniform additive error still tends to zero. Choosing a fixed large λ cutoff and letting it tend to infinity after d proves the all-covolume statement.

The only prior-art conclusion from the targeted and alternate live Google screening is that no matching sparse-adaptive ceiling surfaced. Lean checks the rational separations between the exponents, not the random-lattice or analytic arguments. There is no priority or unrestricted conjecture claim.
