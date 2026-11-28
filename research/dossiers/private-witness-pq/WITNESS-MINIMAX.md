# Fixed-support guessing versus global coding

For one public family over n endpoints, consider a reduction that samples
a size-at-least-r protected support before the transcript and needs it
disjoint from a set C of c exposed endpoints. Even for non-adaptive
choices of C its worst-case avoidance probability is at most

    p* = binom(n-r,c)/binom(n,c).

Proof: average over uniform C; each support S is missed with probability
binom(n-|S|,c)/binom(n,c) ≤ p*. Uniform sampling over all r-subsets meets
p* exactly for every C, by double counting. Any catalog that hits every
admissible transcript has at least ceil(1/p*) witnesses. At the endpoint
minimum n=r+c, equality forces every r-subset to have equal probability
and none to be omitted (each C misses only its own complement).
This is elementary covering arithmetic, not an originality claim.

At c=63 and f=6, r=7 and n=70, this restricted proof pays at least
binom(70,63)=1,198,774,720 in worst-case reciprocal success probability,
independent of choice of code or nonuniform fixed witness weights.
At n=130, density bound falls sharply, but it is still not a statement
about the tightness or security of different proof forms. It does not
apply if a reduction can program a protected direction after observing
exposures, or use an aggregate game instead of guessing a support.

Check: witness_coverage_check.py exhausts both sides of the incidence
identity for n≤9 (165 parameter triples). Next substantive task: try
to exploit the specific structure of multi-recipient hybrid reductions
to replace transcript partitioning by a global game, or give a precise
oracle-model separation. Do not construe this note as a lower bound on
actual security or as a new KEM.

## Exact optimal weights need the full catalog in the common regime

In fact, if r≤min(c,n−c), equality in the average bound implies that
every r-support has exactly the same mass, not just when n=r+c. For
c>0, all larger supports have strictly smaller density (or zero) and
therefore zero mass in an optimizer. All (n−c)-subset sums of weights of
r-supports must then be equal. Here is the elementary full-rank argument.
If all k-subset sums are equal and r≤k≤n−r, compare k-subsets formed
by adding x versus y to the same (k−1)-set disjoint from both. For
g(T)=w(T∪{x})−w(T∪{y}) the (k−1)-subset sums of (r−1)-weights on n−2
points are all zero. Induct on r; admissibility is preserved, and a
constant weight whose subset sum is zero is zero. Thus weights agree
on adjacent r-subsets, and the exchange graph is connected. The base
r=0 is immediate. This is a standard inclusion-matrix rank argument,
not a new combinatorial theorem.

For (n,r,c)=(130,7,63), the optimal reciprocal success is about 121.47,
but achieving it **exactly** by fixed-support sampling uses all
binom(130,7) supports. Compare near-optimal catalog size and the security
reduction's programming costs separately; this does not imply that all
of these supports need be materialized or that every support corresponds
to a distinct public ciphertext component.
