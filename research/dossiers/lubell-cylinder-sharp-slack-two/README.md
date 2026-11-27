# Refuting the proposed Lubell extremizer, and the exact slack-two optimum
Private research; not the ordinary cardinality-product problem. The source is
Wu–Feng, [The Lubell bound for intersecting-union families,
arXiv:2607.07564v1](https://arxiv.org/html/2607.07564v1), Problem 1.3. They
call the fixed-in/fixed-out family a natural candidate, not a conjecture.

For positive t,u, let L_n(F)=sum_{A in F} 1/binom(n,|A|), for families in
which every pair (including equal sets) intersects in at least t and has
union at most n-u. A cylinder forces inclusion of a common t-set and
exclusion of a disjoint u-set.

At n0=t+u+2, assume (by complement symmetry) t≤u. Let T have t elements.
The lower star consists of T and all T∪{j} for j outside T. Its conditions
are immediate. The cylinder and lower star have respective layer counts
(1,2,1) and (1,u+2,0), in layers t,t+1,t+2. Hence the star exceeds the
cylinder by
  u/binom(n0,t+1) - 1/binom(n0,t+2),
which is positive exactly when u(u+1)>t+2. If u≥2 and t≤u, this is always
strict. In particular at t=u=2,n=6 the weights are 4/15 versus 7/30.

Adjoin a free coordinate, taking both copies of each set. The old
intersection bound remains; the union can grow by at most one while n
increases by one. For old size k, reciprocal Pascal says
  1/C(n+1,k) + 1/C(n+1,k+1) = [(n+2)/(n+1)] / C(n,k).
Thus normalized Lubell score L_n/(n+1) remains exactly constant, and the
same strict comparison works at every n≥t+u+2. Free extension of the
cylinder is again the cylinder with the same forced sets. For n=t+u we
have at most one possible family member, and when n=t+u+1 there is at most
one member in each of the only possible layers t,t+1: intersections
force two t-sets to coincide, and unions force two (t+1)-sets to coincide.
The cylinder attains both bounds. Wu–Feng already prove sharpness at
t=u=1 for every n. This completely classifies when the proposed
cylinder is extremal, but does not determine the maximum at larger slack.

## Sharp optimum at slack two
At n=t+u+2 the only sizes are t,t+1,t+2, with at most one outer-layer
member on each side. A lower member forces all middle members to contain
it; an upper member forces all middle members to be contained in it.
If both are present, their inclusion relation is forced by the
intersection condition, and all family members belong to the cylinder
between them. With just the lower outer member there are at most u+2
middle members, achieved by the lower star; with just the upper there
are at most t+2, achieved by the upper star.

If neither is present, the family lies in the middle layer. Two
distinct middle sets must meet in precisely t; write them as
X∪{a},X∪{b}. A third set either contains X, or must contain both a and b
and exactly t−1 elements of X, hence is contained in Y=X∪{a,b}. If a
third set does not contain X, it cannot coexist with X∪{c} for c outside
Y, because their intersection has size t−1. Thus all middle members
contain X or all lie in Y. Their count is at most max(u+2,t+2), and
adjoining the corresponding outer layer preserves admissibility and
strictly increases the Lubell score. So the extremal weight is the
maximum of the cylinder, lower star, and upper star weights.
For t≤u the lower star dominates the upper: it has ≥ middle members
and C(n,t+2)≥C(n,t), since the ratio is
  (u+2)(u+1)/[(t+2)(t+1)].
When max(t,u)≥2 the lower-star comparison already exceeds the
cylinder strictly; if t=u=1 the cylinder wins, consistent with
Wu–Feng's theorem.

## Lean declarations and audit

In LubellClassification.lean:
- IU.Lubell.raw_fails proves the strict comparison in the original Lubell
  sum, with either parameter order, for max(t,u) ≥ 2 and n ≥ t+u+2.
- IU.Lubell.proposed_optimal_iff_short formally classifies extremality of
  this proposed cylinder when max(t,u) ≥ 2.
- IU.Lubell.slack_two_exact_raw proves the exact direct lower-star maximum
  when t ≤ u and u ≥ 2. IU.Lubell.sharp_slack_two transports the theorem
  to the other order by complements.
- The published t=u=1 result is cited, not re-formalized here.

Run ./replay.sh with MATHLIB_DIR set to a built Mathlib checkout at
d13f23b723b8a846827a245b89c10fc7d3f11612 and Lean 4.34.1 on PATH (or set
LEAN_BIN). The script checks all source hashes and uses a fresh output
directory. All final statements use only propext, Classical.choice,
and Quot.sound.

Independent check.py enumerates all maximal weighted cliques in the
original set graph for the 15 ordered positive pairs with 2 ≤ t+u ≤ 6,
at n=t+u+2. It does not use shifting, the Johnson classification, or
Lean-generated arithmetic, and is not part of the trusted proof.
