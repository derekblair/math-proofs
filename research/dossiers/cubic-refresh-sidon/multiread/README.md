# One scalar refresh for two epochs with m reads each

Fix m≥2; degree t=2m−1 Shamir over F_q, distinct nonzero public sites S
of cardinality n≥2m. First epoch nonconstant coefficients are independent
uniform. The second polynomial is first plus uniform, independent λ times
a public nonzero Q of degree ≤2m−1 with zero constant term. Reads concern
current shares only, with old buffers/coins unavailable. For each epoch at
most m sites can be read. We consider perfect transcript privacy in the
ideal share model, not a threshold implementation or new KEM.

Write W=Q/X and V for polynomials of degree at most 2m−2. For a site m-set
A, let R_A be its monic vanishing polynomial, P_A=R_A(0)≠0, and let
U_A=R_A⋅{polynomials of degree at most m−2}⊂V (dimension m−1).
Exactly when
  W ∉ U_A+U_B for every pair of disjoint site m-sets A,B
is the scheme perfectly private.

## Exact obstruction

It suffices to consider full m-sets by padding. Overlapping sets have
union ≤2m−1, so one polynomial with constant 1 vanishing at the union
is a unit-secret witness without using refresh. For disjoint sets, any
unit-secret witness has forms f_A=R_A/P_A+X R_A h_A and
f_B=R_B/P_B+X R_B h_B for deg h_A,h_B≤m−2. Set
  L=(R_B/P_B−R_A/P_A)/X.
If L=R_A g_A+R_B g_B in V, evaluating at each a∈A yields
g_B(a)=1/(P_B a) since R_B(a)≠0. The nonzero polynomial
X g_B−1/P_B of degree at most m−1 would then have m roots, impossible.
Also U_A∩U_B=0 since the combined 2m roots exceed the degree bound in V.
Thus U_A+U_B has codimension one, L has nonzero quotient class, and
f_B−f_A can equal λ XW iff W lies outside that hyperplane. The unit-secret
witness criterion holds because the view is a translate of a fixed
uniform linear image; it implies classically adaptive privacy by
unnormalized fixed-path probabilities, exactly as in the cubic case.

An equivalent useful scalar form is
  Ψ_(A,B)(W) = Σ_(a∈A) W(a)/(R_A'(a) R_B(a)) ≠ 0.
Indeed W is in U_A+U_B iff interpolating the m ratios W(a)/R_B(a)
on A produces a polynomial h_B of degree ≤m−2, as seen by subtracting
R_B h_B from W and factoring R_A. The displayed expression is the top
coefficient of the unique degree ≤m−1 interpolant. This denominator
never vanishes. Reversing A,B negates Ψ, since summing residues for
all roots of R_A R_B gives zero when deg W≤2m−2, by the same top
coefficient argument.

## General lower bound

If W has at least m site roots, choose A among them and B disjoint;
then W∈U_A is forbidden. Thus a secure direction has at most m−1
site roots. Remove its z site roots (z≤m−1), leaving N=n−z sites.
In the root-free case N=n exactly.

Let [j]_q=(q^j−1)/(q−1). Each projected U_A in V/F_q W has
[m−1]_q projective points, because the projection is injective on U_A
when W does not vanish at its sites. A quotient projective point has
exactly q projective representatives outside the direction [W],
which can be normalized as [H+cW], c∈F_q. Distinct normalized
representatives have disjoint sets of retained site roots: a common
root would force W to vanish there. At most one representative in
the pencil can have at least m retained roots, since otherwise one
could take disjoint A and B from their disjoint root sets and get
W in U_A+U_B from their difference. This argument permits overlapping
m-sets within the same representative; it does not collapse those
incidences when they come from a polynomial with more than m roots.

That representative has at most 2m−2 roots, so its total incidence
multiplicity is at most binom(2m−2,m). Counting all incidences gives
  binom(N,m) ≤ binom(2m−2,m) (q^(m−1)+1).
For the sharper count, within each U_A exclude representatives with
an extra retained root. For each possible extra root the exceptional
subspace has dimension m−2 (factor R_A and one more linear factor).
Thus at least [m−1]_q−(N−m)[m−2]_q projective members of each U_A
have exactly m retained roots. Their projections are jointly injective:
inside a single representative the exact root set uniquely identifies
A; distinct representatives in one pencil cannot both have m roots.
Consequently
  binom(N,m) ([m−1]_q−(N−m)[m−2]_q) ≤ [2m−2]_q.
For fixed m and N→∞, the coarse bound implies N/q→0; then the sharper
bound yields q^(m−1)≥(1−o(1)) binom(N,m). This is
q=Ω_m(n^(m/(m−1))) with the specified asymptotic constant. It is
not sharp for m=2 (the Sidon classification is stronger), and for
m≥3 there is an exponent gap to the explicit q=O_m(n^m) subfield
construction described in the prior cubic dossier, using m basis
coefficients on X through X^m. The present proof does not close this
gap or transfer a fixed-m estimate to m growing with n.

## Exact linear-scale infinite diagonal family n=2m

If char(F_q) does not divide m, any 2m distinct nonzero sites admit a
deterministic secure direction, irrespective of their geometry. Put
R=∏_(a∈S)(X−a). At one distinguished site set v(a)=1−2m; at all
other sites set v(a)=1. Then Σ_S v=0 and for any m-set A,
Σ_A v equals m or −m, both nonzero. Interpolate
  W(X)=Σ_(a∈S) v(a) R(X)/(X−a).
Each summand is a monic polynomial times v(a); the degree 2m−1
coefficient is Σ v=0, so W has degree at most 2m−2. At each site,
W(a)=v(a)R'(a). As any disjoint A,B partition S, the obstruction
functional is exactly Σ_A v. This proves privacy. In particular if
2m+1 is an odd prime power, take the whole F_q^* with q=2m+1:
its characteristic cannot divide m and there are exactly 2m sites.
This field size is minimal because n distinct nonzero sites always
need q≥n+1. This gives infinitely many diagonals where the field
lower is only linear in the jointly growing parameters.
No assertion when the characteristic divides m for arbitrary n=2m.

## Dual description of the near-diagonal gap

Write n=2m+δ, R for the full-site polynomial, and
v(a)=W(a)/R'(a). The degree restriction deg W≤2m−2 is equivalent
to the δ+1 constraints Σ_S a^j v(a)=0 for 0≤j≤δ.
One direction follows by interpolation of X^jW and its vanishing
top coefficient. For the converse the δ+1 moment rows are independent
Vandermonde rows, and their solution space and the degree-bounded
evaluation space have the same dimension 2m−1. For omitted site set
D=S\(A∪B) of size δ, the exact obstruction is
  Σ_(a∈A) v(a) ∏_(d∈D)(a−d) ≠ 0
for every m-set A disjoint from D. This follows from
R'(a)=(R_A R_B)'(a)∏_(d∈D)(a−d). This restates the extension question
as an explicit moment-constrained weighted subset-sum design, not a
claim of a construction when δ>0.

## Prior scope

The vanishing-product interpolation and Reed–Solomon/Vandermonde
identities are classical. The convolutional-code comparison is only
conceptual: Almeida–Napp–Pinto construct lower block triangular
Toeplitz superregular matrices (maximal-distance-profile code setup),
https://arxiv.org/abs/1303.3807 ; the Shamir obstruction above asks only
about this specific quotient and exact privacy, not about all their
minors. Standard projective counting: Hirschfeld,
https://academic.oup.com/book/53387/chapter-abstract/422057584 .
Shamir source https://doi.org/10.1145/359168.359176 . The new claims
here are the explicit obstruction, lower incidence bounds and diagonal
construction within this model; priority not established.

The same pencil argument actually injects *all projective polynomials*
with at least m retained roots, independently of the number of m-subsets
within each. Their exact number by binomial sieving is
  Σ_(j=m..2m−2) (−1)^(j−m) binom(j−1,m−1) binom(N,j)[2m−1−j]_q ,
and is at most [2m−2]_q. This uses the elementary threshold sieve identity
1_(u≥m)=Σ_(j=m..u)(−1)^(j−m) binom(j−1,m−1) binom(u,j)
for a polynomial with u retained roots (the usual inclusion-exclusion
formula for at least m events). For m=3 it simplifies to the explicit
bound binom(N,3)(q+1)−3 binom(N,4)≤q³+q²+q+1. The projected U_A
are projective lines in PG(3,q); lines indexed by disjoint triples must
be skew, but overlapping triples can meet. This is not an ordinary
line spread: intersections carry prescribed root-set information, and
arbitrary spread existence does not provide an upper construction.
Compare line spread terminology in
https://doi.org/10.1016/S0012-365X%2896%2900345-7 and higher-order MDS
span-intersection field bounds in https://arxiv.org/abs/2107.10822 and
https://arxiv.org/abs/2212.11262. Those are related design techniques
but impose different intersection constraints; no transfer claimed.

## Verification boundary

The pinned Lean file DiagonalWeights.lean checks the zero total weight and
nonzero m-subset sums for the one-exception construction. It does not
formalize the projective counting, polynomial interpolation or privacy
model. The independent exact replay checks 39,816 diagonal cases and
20,970 comparisons of the moment condition against affine-rank privacy.
Run python3 checks.py to reproduce the replay.

The related full refresh scheme described by [On Regenerating Codes and
Proactive Secret Sharing](https://eprint.iacr.org/2022/096) uses different
refresh and adversary parameters. These bounds are for a single public
direction and one secret fresh field element in two epochs, and are not
claims about a general deployed proactive protocol.
