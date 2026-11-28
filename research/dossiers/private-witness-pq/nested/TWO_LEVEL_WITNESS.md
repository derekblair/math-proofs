# Two-level private witness beating the flat disjoint-cluster bound

## Concrete result

The asymmetric exact-63 probability bound and its attaining cases have a [Lean replay](lean/REPLAY.md). The full guarded security game is a paper proof.

Use ten disjoint clusters of 13 domains each. Within each cluster a
12-of-13 Shamir polynomial carries one offset. The offsets for a
single family are evaluations of an **outer 7-of-10 Shamir polynomial**;
its constant is that family's independent masked offset. Use a field with bijective 32-byte encodings, such as GF(2^256), to
represent 256-bit strings without rounding. Across families, offsets sum
to the plaintext, as in the prior
signed full-context wrapper. Total wire is unchanged at 130
independent masked capsules per family. For any six offline domains
at most three clusters lose two or more members. Recover from the
first seven available clusters, selecting the first 12 available
members within each, always 84 ordinary decapsulations per family.
This is four fewer versus the previous flat layout at the 88 cap.

Quantum-computational component requirements are unchanged: the
trusted aggregate-only CCA game with classical queries, independent
honest fixed roster keys of a surviving good KEM family, PQ PRF,
one-time strong signature, deterministic availability selection and
failure handling, globally charged honest correctness and context
guard, and no same-key legacy/raw API or endpoint/aggregate
implementation compromise. This does not authorize untrusted control
of receiver responses. No end-to-end deployment claim.

## Changing the secret with four paired supports

Choose uniformly four of the ten clusters, then choose independently
a uniform pair of support sites in each. Change the outer constant by
the challenge message difference Δ using the degree-six normalized
product with roots at the six unchosen outer evaluation positions.
The outer change is nonzero at each chosen cluster when Δ≠0. In each
chosen cluster, implement the resulting offset change by a degree-11
normalized root product killing that cluster's other eleven sites.
All endpoint shares outside the eight protected sites are identical.
The shift of the outer and inner coefficients is a bijection between
the uniform sharing spaces of the two possible secrets.

For any final exposure counts e_j in a canonical surviving family,
the probability the private support avoids them all is
  P(e) = e_4(b_1,...,b_10) / [binom(10,4) binom(13,2)^4],
  b_j = binom(13−e_j,2),
where e_4 denotes the fourth elementary symmetric polynomial. The
minimum over legal labelled exposure sets is the minimum over the
integer counts 0≤e_j≤13 and Σe_j≤63; because each b_j is nonincreasing,
one can pad counts to sum exactly 63. Permutation symmetry reduces
to the nondecreasing integer lists. Exhaustive exact enumeration
of 27,523 such lists proves the minimum numerator is 28,140,210,
achieved at seven sixes and three sevens. The denominator is
7,773,161,760, giving λ=4,963/1,370,928 precisely. The code enumerates
sorted lists with explicit remaining-sum bounds and uses the
coefficient of X^4 in ∏_j (1+b_j X). It contains no crypto or endpoint
operations. This is an exact finite computational certification of
the probability, not a Lean formalization or measured security.

This avoidance probability is minimax optimal for *this* symmetric
layout among prior private fixed-coordinate witnesses. For a nonzero
outer shift a degree-six polynomial changes at least four cluster
offsets. Each changed offset needs at least two changed endpoint
coordinates because the inner degree is at most eleven. Any valid
support can be shrunk to four distinct such cluster pairs by choosing
the corresponding root polynomials above; this improves avoidance
weakly. The permutation group on clusters and sites is transitive
on these minimal-support patterns, and symmetrization cannot lower
a worst avoidance probability over all exposed labelled sets. No
optimality claim over different hierarchical layouts/codes or
non-guessing proofs.

## Lifting the active reduction

The actual receiver and key generator do not use or know S. For
each good-family branch the reduction samples S before programming
an independent challenger key, aborts upon actual disclosure of
a protected slot or the whole witness family, and at completion
checks its canonical good-family predicate. For every unchanged
real-source transcript, independently sampled S passes the
disjointness predicate with its exact P(e). In the accepted branch
draw a final coin with probability λ/P(e), computed from its
classical exposure labels; thus the unchanged real restricted
acceptance is precisely λ times the corresponding canonical-family
acceptance. Apply this normalization only in the real sources, not
as a conditioning assertion inside a hybrid.

The prior indexed exact-challenge-capsule substitution and independent
PRF hybrid apply to the eight chosen slots. A protected exact challenge
PRF input is never returned by the guarded aggregate oracle. In the
ideal comparison change only the eight masks by the coefficient
coupling above, retaining the same public body, signature, disclosure
record and allowed responses. The final thinning value is also the
same since it uses only final labels. The resulting multiplier is
2 R * 8 / λ for R candidate families; correctness and guard terms
are separate global additive errors. As before no challenge secret key
is needed to check the final predicate. Exact biased rational coins
can be implemented by rejection sampling or truncated with negligible
extra probability when a bounded runtime definition is required.

For two families, multiplier 43,869,696/4,963≈8,839.35, compared with
approximately 13,817.67 in the best flat model at ≤88 decaps.
This is a 36.03% reduction of that proof factor, simultaneously
84 instead of 88 decaps and the same 130-slot wire. One-block still
has a tighter multiplier but requires 124 decaps. No statistical
or operational security difference inferred from these counts.
Classical recursive threshold composition is prior, e.g. the
Benaloh–Leichter monotone access-structure construction, and
compartmented partial-secret recovery has known antecedents; see
https://www.cs.cornell.edu/courses/cs754/2001fa/bena88.pdf and
https://researchonline.jcu.edu.au/362/ . This improves the earlier proof tradeoff in this model. No priority
claim for Shamir concatenation, new primitive, or absolute first result.

## Sharper asymmetric point, same wire and at most 85 decaps

Make just one of the ten clusters 13-of-13, retaining 12-of-13
in the other nine and 7-of-10 outside. Four disabled clusters
consume at least 1+2+2+2=7 outages, so six outages again leave
seven qualified clusters. Prefer the regular qualified clusters,
then use the special cluster if needed. Honest recovery uses
either 84 regular decaps or 6·12+13=85 decaps. The total wire
is still 130 sites per family.

The reduction chooses a private support that includes the special
cluster with probability q, where that mode selects the special
and three uniform regular clusters; with probability 1−q it
selects four uniform regular clusters. The special cluster
requires only one changed share (its local complement has
12 roots, allowed at degree 12); regular clusters still require
two changed shares. Thus 7 or 8 protected slots. Use
`s` exposures on the special cluster, and let
b_i=binom(13−e_i,2) on the nine regular ones. The two avoidance
probabilities on an exposure set are
  A(e) = e_4(b)/(binom(9,4)·78^4)
  B(s,e) = [(13−s)/13]·e_3(b)/(binom(9,3)·78^3).
Minimize (1−q)A+qB over s+Σe_i=63. Exposure-label thinning uses that minimum divided by the exact
mixed avoidance probability (1−q)A+qB in either mode, before
conditioning on survival. Neither A nor B needs to be positive by itself.

The guard/correctness error terms remain globally charged. In the
difference of unnormalized restricted acceptances, take terms
separately conditional on the proof's mode, without conditioning
on actual disjointness. The 7-hybrid and 8-hybrid losses then
average with initial mode probabilities q and 1−q. Each mode's
ideal comparison still preserves the entire final record, so
the mixed two-family multiplier is 4(8−q)/p_min. This is not
assuming the modes remain balanced *after* early abort.

The exact best q for this layout and comparison is
  q=5,077,873/9,816,373,
  p_min=106,948,625/24,647,510,264.
Here `special.py` exhausts 174,261 allocations (sort the
nine regular exposure counts and enumerate s separately).
Two witness exposures are tied at that q:
- s=0, all nine regular exposure counts are 7;
- s=13, regular counts are four 5s and five 6s.
Their affine avoidance functions cross at exactly the stated q.
The first affine function divided by (8−q) is increasing,
and the second is decreasing, so their pointwise minimum
upper-bounds the attainable p_min/(8−q) for all q and is
maximized precisely at the intersection. The enumeration
verifies no other allocation is worse there. This proves the
best choice in the two-mode strategy without floating fitting.

The two-family multiplier is 5,164,047,515,744 / 748,640,375
≈6,897.90, about 50.08% below the prior flat 13,817.67
comparison, with worst 85 rather than 88 decaps. Since any
valid outer shift has at least four changed cluster offsets,
shrinking supports and independently symmetrizing equal
clusters reduces arbitrary fixed-coordinate witness laws in
this layout to these two mixture modes for the objective of
worst avoidance divided by expected support size. This is
still not an optimum over layouts, proof techniques, or
different cryptographic primitives.

The unchanged 130-slot independent examples use, before
global signature, nonce and framing, 145,600 bytes for
one ML-KEM-768 family and 1,316,900 for ML-KEM-768 plus
HQC-3, i.e. 32-byte masks plus 1,088- or 8,978-byte capsules
respectively. Sources: FIPS 203 https://csrc.nist.gov/pubs/fips/203/final
and the HQC authors' October 2026 Table 9
https://pqc-hqc.org/doc/hqc_specifications_2026_10_12.pdf .
This architecture does not change the base KEM assumption,
quantum security category or real endpoint hardening.
