# Exact slack-parameter algorithm for intersection–union families

For positive t,u and s=n−t−u≥0, the maximum of any nonnegative
rank-weighted objective on (t,u)-families is the maximum-weight clique
in a graph depending only on s, with at most
(s+1)(floor(s/2)+1)2^s vertices. This gives an exact fixed-parameter
algorithm for the cardinality problem and the factored raw Lubell sum.
The original subset graph can have exponentially many vertices even
with s fixed. This is a restricted-parameter result and not a general
polynomial-time maximum clique claim.

## Exact reduction

Shift an optimal family left, preserving both validity and the number
of sets of every size. Write r_A=t−|A∩[t]|, M_A for its membership mask
on the next s positions, j_A=|A|−t. For a pair, put e=max(0,j_A+j_B−s).
The usual shifted prefix certificate is that for some i the sum of
the two prefix counts is at least i+t+e. It follows by optimizing
over all left shifts of B: if every prefix defect is less than t+e,
take the |B| leftmost elements of ([n]\A) union the t+e−1 leftmost
elements of A. The prefix capacities dominate that of B, yet this
replacement intersects A too little to meet the required intersection
or union constraint. This is the same argument as FamilyPrefix and
PrefixBridge in the earlier Lean dossier.

Because each prefix count is at most i, every witnessing i is at
least t. Because their sum is at most 2t+j_A+j_B, it is at most
t+min(s,j_A+j_B). Write i=t+h. The normalized condition is

    e+r_A+r_B+h ≤ popcount(M_A mod 2^h)+popcount(M_B mod 2^h).

For self pairs this implies r_A≤floor(s/2). The number of sites
after the middle block is u, and the profile yields
exactly choose(t,r_A)·choose(u,j_A+r_A−|M_A|) original sets. A binomial
coefficient outside its combinatorial range is zero. Two profiles
are adjacent precisely when the displayed condition holds; retain
only feasible-for-some-parameters self-compatible profiles.
The displayed condition is sufficient for the two constraints even
before shifting, by inclusion–exclusion within the witness prefix
and the size identity for union. Thus every clique lifts to the
union of full profile fibers; each original optimal shifted family
maps into a clique; nonnegative weights mean filling fibers cannot
hurt. This proves equality, not just an upper bound.

The number of graph nodes is at most the given function of s. For
uniform cardinality and factored Lubell, the arithmetic on fixed
profiles uses binomial coefficients with bottom O(s) and O(s)
small products. For Lubell a common positive factor is t!u!/n!,
with the leftover multipliers (t+1)…(t+j)(u+1)…(u+s−j). Returning the
raw fully expanded rational can have large output bit length; the
factored form avoids this. For arbitrary input rank weights, add
the exact arithmetic cost of those weights. This yields
2^{O(s²2^s)} poly(s,log n,input-weight bits) bit complexity with a
simple exhaustive clique search and factored output.

Primary rediscovery check: Frankl–Wang JCTA 217 (2026) 106100 already
use shifting and cardinality for short slack; the argument does not
claim priority for shifting or prefix witnesses. Wu–Feng arXiv:2607.07564v1
is the weighted target. No absolute priority claim for the reduction.

## New sharp weighted consequences, exact finite polynomial certificates

Order t≤u, with max(t,u)≥2. For s=4,5,6,7 there are 31/62/150/300 universal
profiles and 22/105/1648/79620 maximal cliques, respectively. In each case
two simple constructions suffice. The low construction fixes a
t-set and takes extras on u+s sites. For s=4 or 6 take all extras
up to s/2. For odd s=5,7 take all extras of size≤⌊s/2⌋ and the extras of
size ⌊s/2⌋+1 containing a single fixed extra site. The product construction
uses disjoint blocks of lengths t+2 and u+s−2. On the first
block take all sets of size≥t+1. For s=4 take all subsets of
size≤1 on the second; for s=6 take all of size≤2; for s=5 take
all subsets of size≤1 and all pairs containing a fixed site;
for s=7 take all subsets of size≤2 and all triples containing a fixed
site in the second block. They are all directly valid.

For s=4 and 5 the low score dominates exactly on u≥2t−1 among
the allowed parameters. For s=6 and 7 it dominates on u≥3t−3.
For t=1 the low construction is always optimal in the scope.
For t=u a reflected product can have the same score as the product;
no uniqueness is asserted. Numerical dominance here refers only to
the scores of the two displayed constructions.

To check the upper bound it suffices to compare every maximal clique
with the specified candidate, since all weights are nonnegative.
After removing t!u!/n!, a clique weight is a polynomial in t,u:
sum, over its profiles, of choose(t,r)choose(u,z)(t+1)⋯(t+j)
times (u+1)⋯(u+s−j). The total degrees are bounded by 6/7/9/10 for
s=4/5/6/7, respectively. In general r+z≤floor(s/2): for a self witness
2r+e+h≤2p, where p≤h counts prefix ones within the mask and p≤|M|.
Thus 2r+e≤|M| and r+z=j+2r−|M|≤j−e≤floor(s/2).
Cover the integer cone by the following affine parameterizations
with arbitrary a,b≥0:

* t=1: (1,2+b), use low for all.
* s=4,5: (2+a,3+2a+b) low; (2+a+b,2+2a+b) product.
* s=6,7: (2+a,3+3a+b) low; (2+a+b,2+3a+b) and
  (3+a+b,4+3a+b) product, by parity of u−t.

For each clique difference and each cone, evaluate the polynomial
on the square grid [0,d]^2; form forward differences in both
coordinates. All computed coefficients are nonnegative. The
two-variable Newton identity expands the difference as a sum
of those coefficients times choose(a,i)choose(b,j), so the check
covers every pair in each unbounded cone. This proof does not use
the Complete Intersection Theorem. The small deterministic Python
certificates are not Lean verification. The generic exact optimization equivalence and compact graph bound
are Lean checked separately (see Equivalence.lean and
Compact.lean). Specific polynomial tables and finite search
for the four slack values are not fully Lean checked yet.


## Reproduction

Run the Lean proof separately with `MATHLIB_DIR` pointing to a built
Mathlib checkout at d13f23b723b8a846827a245b89c10fc7d3f11612,
`LEAN_BIN` pointing to Lean 4.34.1, and `bash replay.sh`. Its clean
replay uses an empty local output folder. Lean does not trust
or import the Python enumeration.

Run `python3 certify.py` for excess 4–6, `python3 fast_newton.py`
(Python with NumPy) for excess 7, and `python3 independent.py` for
independent clique enumeration, exact polynomial-grid witness layer counts,
and two original-graph
weighted controls. The NumPy integer bounds are checked before every
multiplication to exclude arithmetic overflow.

Use `quotient.solve_factored(t,u,s)` for a normalized integer numerator
and a compressed witness, without expanding the factorial multiplier.
