# Exact projective Sidon classification of cubic one-coin refresh

Continuation of the [field-size result](README.md). Same assumptions: n≥4 nonzero sites in F_q,
degree three, two current reads each in two epochs, one fixed public refresh
direction Q. Write W=Q/X≠0 and homogenize W to a binary quadratic (so a linear
polynomial has a root at infinity and a constant has a double root there).
Call a site exceptional if W vanishes there. A viable direction never has
two exceptional sites: their pair polynomial would equal [W], lying on a
forbidden secant with any disjoint pair.

## Classification

For at most one exceptional site, form one label z_a for each remaining
(regular) site a. In the following table, q denotes the field size.

| Roots of the homogeneous W | Label z_a | Group operation for a pair |
|---|---|---|
| Double at infinity | a | addition in F_q |
| Double finite root r | 1/(r−a) | addition in F_q |
| Distinct roots r,s in F_q, both finite | (r−a)/(s−a) | multiplication in F_q^* |
| Distinct roots r and infinity | r−a | multiplication in F_q^* |
| Conjugate roots r,r^q in F_(q²) not in F_q | (r−a)/(r^q−a) | multiplication in norm-one subgroup of F_(q²)^*, order q+1 |

The labels are injective on regular sites (reciprocal, affine or Möbius
maps). Exactly the following designs are secure: the regular labels form
a *weak Sidon set*, meaning that the pair operation gives distinct results
for all unordered pairs of distinct regular labels. No conditions on
diagonal pairs are needed.

Proof: the projective line through [W] and [R_A] is the class of R_A in the
projective line of V/F_q W, where V is the three-dimensional space of
homogeneous quadratics. Equivalently two pair polynomials land at the same
projection iff the two quotient classes are proportional. For distinct
finite F_q roots the quotient coordinates are (R_A(r),R_A(s)), with ratios
factoring as asserted; the common evaluation kernel is F_q W. At infinity
evaluate the homogeneous polynomial at (1,0), i.e. take its leading
coefficient. If infinity is paired with finite r, evaluation there is
one for monic R_A, giving the stated product. In the conjugate case, the
F_q-linear map R↦R(r) into F_(q²) has kernel F_q W. For nonzero R(r),
its class modulo F_q^* is equivalently R(r)/R(r)^q: equality of those
ratios means their quotient is Frobenius-fixed and conversely. The result
is norm one and the map is onto the group of order q+1. It factors into
the listed site labels. For double finite root r use quotient coordinates
(R_A(r),R'_A(r)); their vanishing is exactly divisibility by (X−r)^2
even in characteristic two by expansion around r. Since the value is
nonzero for regular pairs, the derivative/value ratio is the pair sum of
reciprocal differences. For a double root at infinity the leading and
next coefficient give the negative of the ordinary pair sum (negation
does not affect equality).

Two distinct regular pairs that share a site can never have the same
projection, either by cancellation of the site label or by the common
root argument. Two distinct pairs incident to the exceptional site do
share one reserved line, but they share that site and are not disjoint.
No regular pair has that reserved line, since the quotient evaluation
at the exceptional site is nonzero for every regular pair. Hence the
prohibited disjoint-pair collision is precisely a regular weak Sidon
collision. This remains true for characteristic two and all degeneracies
listed in the table.

## Strengthened field lower bounds outside binary additive type

Let m be the number of regular labels (m=n or n−1). In an abelian
group G with at most one nonidentity involution, a weak Sidon set of
size m satisfies
  |G| ≥ m(m−1)−2m+1−ι,
where ι∈{0,1} counts nonidentity involutions.
Write the operation additively for the proof. Count m(m−1) ordered nonzero
differences as edges x→x+δ with x,x+δ in the set. Two distinct edges of
the same nonzero δ must be consecutive or reversed: if they are disjoint,
x→y and u→v gives the forbidden x+v=y+u; sharing a start or end forces
equality as edges. A nonreversal consecutive pair is a progression with
distinct endpoints, whose midpoint determines the two endpoints uniquely
as an unordered pair by the weak Sidon condition. Each such midpoint
therefore contributes at most two unordered edge collisions, one for
each direction. This charge applies even in order 3: a directed triangle
charges its three distinct midpoints. Reversals are only possible for
the single involutive difference, and at most one reversed pair is
possible, since two distinct undirected edges of that difference would
be disjoint and give a collision. Thus there are ≤2m+ι unordered
same-difference edge collisions total. Each difference of multiplicity
u contributes u−1 repeated uses, at most binom(u,2), leaving at least
m(m−1)−2m−ι distinct nonzero differences. Including the identity proves
the bound. There is no appeal to an interval Sidon bound.

The cyclic multiplicative groups in the table satisfy the involution
hypothesis in all characteristics; the additive group satisfies it when
q is odd. Consequently q≥m²−3m−1 in every non-binary-additive case
(in fact +1 for additive odd, +1 for split odd, +2 for split even,
−1 for irreducible odd and 0 for irreducible even, by using group sizes
and involution counts). Since m≥n−1, this is q≥(n−1)²−3(n−1)−1
for n≥4. In the double-root characteristic-two group every element is
its own inverse, and each restricted pair sum is nonzero. Here the bound
is q≥1+binom(m,2), and the reversed-edge argument does not give a
leading constant 1. The quadratic exponent remains sharp in all cases
where an explicit family is exhibited; no assertion that the leading
constant is sharp for double-root characteristic two.

## Prior boundary

Weak Sidon restricted sums and the progression charge for repeated
differences have classical antecedents, e.g. Ruzsa's original discussion
https://matwbn.icm.edu.pl/ksiazki/aa/aa65/aa6537.pdf , and the analogous
progression argument for integer intervals in Balogh, Füredi and Roy
https://real.mtak.hu/164304/1/2103.15850v2.pdf . The application to the
refresh direction via quadratic root type, particularly the exceptional
site and norm-one branches, is the content here; there is no priority
claim for the additive-combinatoric bound, field geometry or a KEM.

## Exact available labels and converse constructions

Each row is also a recipe for importing weak Sidon sets from its group.
The label image for allowed regular sites is precisely:
- double infinity: F_q minus 0;
- double finite r: F_q minus 0 and, if r≠0, minus 1/r;
- split finite r,s: F_q^* minus 1 and, if both roots are nonzero, minus r/s;
- split r,infinity: F_q^* minus r if r≠0, otherwise all of F_q^*;
- conjugate roots: norm-one group minus 1 and r/r^q.

These exclusions follow by extending each label map to the projective site
line: 0 and infinity are not allowed share sites, and rational roots
map outside the target group (except that infinity maps to 0 under the
finite double-root reciprocal map, which is handled as an excluded site).
The norm-one map is a bijection from the entire projective line, by
Möbius injectivity and matching orders. Whenever permitted, one nonzero
site root of W may be adjoined, but not both roots of a split W.
A group translate of any m-set can avoid up to two excluded symbols
when |G|>2m: each forbidden symbol rules out at most m translates.

Concrete binary bridge: in an elementary abelian 2-group of order q,
translate a weak Sidon m-set to contain zero. Represent its remaining
m−1 elements as distinct nonzero binary parity-check columns. The weak
Sidon property is equivalent to no set of at most four columns having
zero sum: one- and two-column dependencies are already excluded;
three columns would collide with a pair containing zero; four would
collide across two disjoint pairs. Conversely, any pair collision
gives such a dependency. Thus the corresponding binary linear code
has minimum distance at least five (or is the zero code with no
nonzero words). The Hamming sphere bound for radius two gives
q≥1+(m−1)+binom(m−1,2)=1+binom(m,2), even if the parity-check matrix
is not full rank.

For square q=s² with s>2, one can explicitly use n=s+1 sites with W
a double finite nonzero root. In the additive group F_s² choose the
m=s labels (x,x²) in odd characteristic, or (x,x³) in characteristic
two. A distinct pair sum gives x+y and xy in both cases, since
(x+y)²−(x²+y²)=2xy in odd characteristic and
x³+y³=(x+y)³+(x+y)xy with x+y≠0 in characteristic two.
It therefore determines the unordered roots. Translate the label set
to avoid 0 and 1/r, possible since q>2s; lift by a=r−1/z, and add the
one exceptional site a=r. This explicit size improves the base-field
matrix example's s−1 nonzero site count. No claim of optimal small
parameters beyond the stated examples and bounds.

Exact minima for the first three n:
- n=4: q=5, sites {1,2,3,4}, W=1−X; q≥n+1 by site distinctness.
- n=5: q=7, sites {1,2,3,5,6}, W=1−X; the geometric lower bound
  q≥6 rounds up to the next field size 7.
- n=6: q=11, sites {2,4,5,6,7,8}, W=3(X−2)²; q≥10 rounds up to 11.
An additional characteristic-two example is n=5, q=8 with W=(X−1)²
and sites 1,4,7,6,2 in binary polynomial encoding modulo X³+X+1.
The separate finite checks compare the classification against the
projective obstruction, and this binary example directly to the affine
privacy rank equation.
Independent indexed determinant witnesses (Lean compiler outcome separate):
GF(5) {1,2,3,4}, W=1+X; GF(7) {1,2,4,5,6}, W=1+X;
GF(11) {1,2,3,7,9,10}, W=1+X+3X².

n=7 has exact minimum q=16. The lower is q≥binom(6,2)=15, and 15
is not a prime power. In the additive group F_2^4 the following six
binary labels form a weak Sidon set:
{0,e1,e2,e3,e4,e1+e2+e3+e4}. The five nonzero vectors have no dependence
of length at most four: their only nonempty dependence is the sum
of all five. Translate by e1+e2 (bit integer 3), producing labels
{3,2,1,7,11,12}, avoiding 0 and bit integer 4. In any polynomial
basis identifying these bit vectors with F_16, take r=1/4,
W=(X−r)^2 and lift each label z to a=r+1/z, then append exceptional
site r. The forbidden labels are avoided; this gives seven distinct
nonzero sites. The script directly checks the privacy rank equation.

Checking a fixed direction and site roster can now use only O(n²) group
operations and a sort of the O(n²) regular pair labels, instead of
enumerating O(n⁴) disjoint views. One needs the root type/roots over the
quadratic extension and a fixed canonical encoding for equality/sorting
of labels; field factorization cost is separate. This is a verification
speedup for this scoped instance, not a general refresh-schedule algorithm.
