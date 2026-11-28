# Exact private hidden-support minimax with disjoint Shamir clusters

## Inherited encryption and query assumptions

This changes the reduction only for any given layout. The active
PQ wrapper remains the same: independently generated endpoint/family
keys under immutable authenticated indexing, one KEM/PRF-slot mask
per coordinate, exact whole-context one-time signature guard, and
classical adaptive ciphertext/decryption or endpoint/family disclosure
requests from an internally quantum adversary. No same-key external
decap API, aggregate-output compromise, malicious endpoint codes,
secret-dependent selection, or timing channels are covered. Assume
at least one computationally good family remains undisclosed. Within
a family the plaintext is shared as the sum of independent Shamir
cluster offsets; cluster j uses n_j≥r sites and k_j=n_j−f
as interpolation threshold, r=f+1. Total receiver decaps/family
D=Σ_j k_j is computed with fixed availability-only selection.
The standard guard and aggregate correctness terms are charged
globally before selecting private witnesses (not inflated by guessing).
Thresholds and the same construction work regardless of whether the
proof uses catalogue selection, canonical credit selection, or minimax.

## Initial canonical-credit proof and exact DP

Let 1≤h_j≤k_j, Σ h_j=c+1. Any legal record's intact good family
has a cluster with e_j≤h_j−1; choose canonical first such cluster.
For that cluster pad its exposed set to h_j−1 (proof only). Set
  a_j = 1/p_j(h_j−1),
  p_j(e)=binom(n_j−e,r)/binom(n_j,r),
with binom zero for numerator below r. Privately choose j with
probability a_j/Σa and then S uniformly an r-set of cluster j.
For every real transcript belonging to its canonical family,
the probability that j is its canonical deficient cluster and S
misses the padded set is exactly (a_j/Σa) p_j(h_j−1)=1/Σa.
Thus proof thinning works even after interleaved adaptive disclosures.
No private key is needed to classify a transcript: only disclosed
families and endpoint labels are read. Early abort only if an actual
disclosure hits the chosen protected S or its family; padding and
canonical selection are applied at the final event. In the real
key-consistent guarded experiment the witness is independent of all
actual cryptographic response values. In the ideal experiment,
a fixed S of size r allows the shift polynomial
  Δ∏_(a in cluster j outside S)(1−X/a)
of degree k_j−1 to change that one offset and leave all unprotected
share coordinates identical. Only protected PRF pads at the forbidden
challenge context are adjusted in the coupling. As in the one-block
proof, the r single-KEM and PRF replacements handle exact same indexed
challenge components consistently, then forward only different local
components and preserve deterministic receiver behavior. The additive
telescoping advantage comparison is 2Rr Σa times component advantages
for R candidate families, plus globally charged guard and correctness.
It is not a claim about maximum security-reduction efficiency.

For H=c+1 and slack s=k_j−h_j≥0, each group costs h_j+f+s
slots, h_j+s decaps, and a_j=binom(h_j+f+s,r)/binom(f+s+1,r).
Scaled-integer DP over group count, total h, and total s minimizes
Σa exactly within this canonical formula under integer wire/decoder
caps. In the n≤130, D≤88 example with c=63,f=6, minimum is
36,722,368/35,061≈1047.385 for six (n,h,k)=(9,3,3) groups
and one (76,46,70). The previous fixed catalogue layout gives
17,612/11≈1601.091 by this same simpler proof, versus 4,678
explicit catalogued witnesses. A slope-calibrated choice of cluster
using the next section's probabilities but anchored at h_j−1
achieves a better explicit formula, included in the addendum.

## Exact layout-wise fixed-support minimax by water filling

One can drop the credits and canonical cluster predicate entirely.
Privately choose cluster j under a mixture q, then choose an
independently uniform r-support there. For exposure counts e_j,
the chance of disjointness is P_q(e)=Σ q_j p_j(e_j). The endpoint
budget is Σe_j≤c (external inactive sites may be ignored or padded).
For any layout with D>c>0, let pbar_j be piecewise-linear interpolation
of the integer p_j values. It is strictly decreasing from 1 at zero
to 0 at k_j and constant zero thereafter; convexity follows from
the decreasing discrete drops
  Δ_j(e)=p_j(e)−p_j(e+1)=binom(n_j−e−1,r−1)/binom(n_j,r)
for 0≤e<k_j and 0 after that. Let e_j(λ) be the unique inverse
on [0,k_j] for λ∈[0,1]. There is a unique λ∈(0,1) with
  Σ_j e_j(λ)=c.
This λ is exactly max_q min_e P_q(e).

Lower: take any supporting line with negative slope −d_j for
pbar_j at e_j(λ) (one adjacent slope suffices at an integer).
Choose q_j=(1/d_j)/(Σ_i 1/d_i). Summing the inequalities
pbar_j(e_j)≥λ−d_j(e_j−e_j(λ)) with these weights makes the
total linear term nonnegative whenever Σe_j≤c. Hence ≥λ.

Upper: write e_j(λ)=b_j+θ_j with b_j=floor(e_j(λ)).
The fractional coordinates θ_j∈[0,1] sum to the integer
c−Σ b_j. They are a convex combination of zero/one vectors with
that exact count. Elementary proof: while two coordinates are
strictly fractional, move in the (+1,−1) direction to the first
boundary in either sign; the original vector is a convex
combination of those endpoints, each with more integral
coordinates. A single fractional coordinate cannot remain.
Taking the corresponding randomly rounded exposure counts gives
exact total c and expected p_j value equal to λ in every cluster,
by local linear interpolation. For any q some actual exposure
vector thus yields Σ q_j p_j≤λ. This upper is an existence
distribution in the proof, not an operational sampling method.
If c=0 the value is 1 for every layout; if c≥D it is 0 since
all clusters can be brought to e_j≥k_j. The bounds above concern
fixed-support proof avoidance; the latter all-covered allocation
also reconstructs the underlying sharing if other families'
shares are fully accessible. The r=1 case reduces to uniform
site sampling and value 1−c/Σ n_j.

Scope of optimality: among arbitrary distributions on local
r-supports, not just those uniform conditional on cluster,
symmetrizing by independent uniform permutations within clusters
cannot worsen their worst avoidance probability, because the
adversary can choose any labelled domains. A valid fixed-coordinate
sharing change of a nonzero secret must alter the constant of
at least one cluster; a nonzero polynomial of degree≤k_j−1
changes ≥r distinct evaluation positions in that cluster.
Any multi-cluster support therefore contains a valid size-r
support in one such cluster, and shrinking to it only improves
avoidance. This proves minimax over prior private fixed-support
witnesses for the stated disjoint Shamir construction, not over
all cryptographic reductions, nonlocal secret-sharing codes, or
overlapping layouts. Any programmed support chosen after seeing
disclosures is outside this argument.

To use λ in the actual hybrid, condition on nothing. In the
unchanged real experiment privately drawn S misses the actual
final label set with probability P_q(e) for that record.
After the usual early abort, add a final independent acceptance
coin of probability λ/P_q(e), using only public parameters and
recorded labels. The probability of survival plus this extra
acceptance is exactly λ for every fixed record, so the unmodified
real acceptance of the canonical good family equals its restricted
acceptance divided by λ. In the ideal-world comparison the final
thinning value agrees under the masked-offset coupling because
both records have the same labels. Ratios here are exact rationals
for all implemented layouts and can be sampled with exact biased
coin methods, or approximated with negligible total error if a
strictly bounded probabilistic runtime is required. The final factor is
2Rr/λ times component advantage, in addition to unchanged
global guard/correctness terms. The support and thinning coin
are not used by encryption, endpoints, signed context or decoder.

## Exact layout optimization

For fixed candidate level λ, define demand g_λ(n)=e(λ) for a
cluster of size n. A layout's true level is ≥λ iff
Σ_j g_λ(n_j)≥c. This is an additive integer layout DP over group
count G and total n with n_j≥r, n≤N and c<n−Gf≤D_cap.
For fixed (G,n), maximize total demand by adding one cluster size
and looking up the state for (G−1,n−n_j). Exact rational arithmetic
or a common denominator suffices. To certify a proposed layout,
calculate its exact level by breaking at its rational p-values,
then certify with the same DP that the maximum demand for all
feasible layouts is exactly c. This is a global optimum for the
specified layout family and receiver/wire cap.

The simple verifier can iterate from any feasible layout: solve
its exact level then choose the max-demand layout there. If the
maximum demand exceeds c its level strictly increases; otherwise
optimality is certified. It is finite but not claimed polynomial
in number of iterations. A polynomial-in-N alternative uses
separation of rational levels. On each segment the slope magnitude
of g_λ(n) is binom(n,r)/B with B=binom(n−e−1,r−1)≤2^N.
Intercepts have the same denominator. With at most N groups,
clearing denominators by their product bounds a level's reduced
denominator by M=N·2^(N²+N). Two distinct levels differ by at
least 1/M². Thus O(N²) rational bisection steps with the exact
optimization DP find a feasible lower-level layout whose own
exact level must be the largest. An exact final certificate is
still available. All complexity here is polynomial in N, not in
binary encoding length of N for an implicit massive roster.

## Concrete exact results

At c=63,f=6,N=130:
| Recovery cap | Best sites used | Actual decaps/family | Exact reciprocal λ |
|---|---:|---:|---:|
| 64 | 130 | 64 | 7,788 |
| 76 | 130 | 76 | 35,321/31 |
| 82 | 130 | 82 | 26,702/37 |
| 88 | 130 | 88 | 21,220/43 |
| 100 | 130 | 100 | 5,750/21 |
| 112 | 130 | 112 | 544,193/3,111 |
| 124 | 130 | 124 | 5,461,000/44,957 |

At cap 88, optimal sizes are (16,18,18,18,18,21,21), all
k_j=n_j−6. The older 4,678-catalogue layout with exactly
the same 130/88 site/decap costs has private minimax
21,590/43≈502.093 without changing any ciphertext or decoder.
The globally optimized disjoint layout gives 21,220/43≈493.488,
a two-family hybrid factor about 13,817.674, versus prior
2·2·7·4678=130,984, about 9.48×. One 130-site full-threshold
block still achieves 121.472 reciprocal, factor ≈3401.206,
but selects 124 decaps/family. All ratios concern reduction loss,
not observed security, throughput or latency. Same wire count
means same 1,316,900 pre-nonce/signature/framing bytes in the
previous independent ML-KEM-768/HQC-3 two-family example.
See FIPS 203 and HQC author October 2026 Table 9 for underlying
sizes, not a claim to beat standardized native wire/security.

Prior parameters and active proof are inherited. Convex allocation
and pairwise rounding are classical; compare Federgruen–Groenevelt,
https://pubsonline.informs.org/doi/abs/10.1287/opre.34.6.909 ,
and Gandhi–Khuller–Parthasarathy–Srinivasan,
https://www.cs.umd.edu/~srin/PDF/2005/depround-dec05.pdf .
No priority claim, new primitive, security certification, or
deployment recommendation.

### Addendum: explicit credit-based slope formula

Let s_j=k_j−h_j as before and S=Σ s_j. Use
q_j proportional to 1/Δ_j(h_j−1) rather than 1/p_j(h_j−1),
and do not require canonical cluster; use final thinning with
the exact worst value. The first h_j−1 increments of exposure
in each cluster reduce q_j p_j by at least a common threshold t;
the next increment has value exactly t, and all later increments
have value at most t. The maximizing integer budget among all
clusters has the following count: there are H−G
strictly-or-weakly larger initial increments and G threshold
increments; c=H−1 spends all but one of the latter. Monotone
marginals allow this allocation and upper-bound any improvement
by the ordered sum of the c largest values. The resulting minimum
probability is Σ q_j p_j(h_j)+t. Since
p_j(h_j)/Δ_j(h_j−1)=s_j/r and
1/Δ_j(h_j−1)=(r+s_j)/(r p_j(h_j−1)), reciprocal is
  [Σ_j (r+s_j)/p_j(h_j−1)]/(r+S).
Encode the numerator using the same credit DP local costs
multiplied by r+s_j; at fixed S divide only in final comparisons.
Best at cap 88 is 32,275/62≈520.565 (groups 15,15 and five 20s).
The water-fill optimum can be stronger because it does not
restrict the equalized slopes to credit anchors.

For the optimal cap-88 layout, one exact supporting-slope sampler
assigns 715/5305 to the 16-site cluster, 663/5305 to each 18-site
cluster, and 969/5305 to each 21-site cluster. Reproduce with
`python waterfill.py` (exact DP) and `python checks.py`.
The checks compare 1,458 exact worst-allocation enumerations for
the supporting slopes, 239 exhaustive small layout optimizations,
and the large exact certificate at λ=43/21220 (maximum demand=63).
The canonical and credit-slope arithmetic can be replayed with
`python pareto.py` and `python marginal.py`, respectively.
