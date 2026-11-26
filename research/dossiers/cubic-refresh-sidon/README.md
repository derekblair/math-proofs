# Sharp quadratic field scale for minimal cubic Shamir refresh

The exact [Sidon classification](SIDON_CLASSIFICATION.md) sharpens the
counting result and identifies the minimum fields as 5, 7, 11, and 16 for
4, 5, 6, and 7 sites. It also gives a pair-label verification algorithm
and a direct connection to binary distance-five codes.

## Setup and result
Let S contain n≥4 distinct nonzero sites of the finite field F of order q.
One degree-at-most-three Shamir polynomial f with uniform initial nonconstant
coefficients carries its secret f(0) across two epochs. At the boundary
refresher replaces f by f+λQ for uniform independent λ∈F and one fixed
nonzero Q of degree ≤3 and Q(0)=0. A passive observer reads at most two
current sites each epoch; old buffers are erased, no refresher coins or
auxiliary outputs are observable. The perfect privacy criterion for any
fixed read pattern is a unit-secret history that vanishes at its read
locations: view = s*v + linear uniform mask, so distributions across s
coincide iff v is in the mask image. For classically adaptive reads this
pointwise criterion suffices by the fixed-path argument (a transcript
of adaptive reads has the fixed-path probability if its labels agree
with prior responses, zero otherwise). No active or deployed KEM claim.

**Theorem.** Any secure one-coin cubic refresh, even choosing arbitrary
n sites and arbitrary refresh direction Q, requires q≥binom(n−1,2).
If Q/X has no site roots, q≥binom(n,2)−1. Conversely for every prime
power s≥n+1 there is an explicit solution over F_(s²) on n subfield sites,
so the optimal field size is Θ(n²). This contrasts with an n-site
ordinary Shamir polynomial (linear field scale) and with high-degree
generic field estimates. The interval inequality t+Σd≥Σb holds here
with equality over the two epochs; it cannot be field-independent
even after optimizing the sites.

## Exact criterion for two pairs
It suffices to consider two sites per epoch, since shorter choices
can be padded and marginalized. If the two pairs intersect, their
union has size ≤3, so a single constant-one root product vanishes
on the union and no refresh is needed. For disjoint read pairs A,B,
let R_A(X)=∏_(a∈A)(X−a), R_B similarly, and P_A=R_A(0), P_B=R_B(0)
nonzero. With unit secret, the two candidate polynomials have forms
f_A=R_A*(1/P_A+αX), f_B=R_B*(1/P_B+βX). Thus their difference divided
by X is L+βR_B−αR_A, where L=(R_B/P_B−R_A/P_A)/X.

In the three-dimensional vector space V of degree-at-most-two
polynomials, L is not in span(R_A,R_B). For if L=u R_A+v R_B,
at each root a of R_A this would give v=1/(P_B a) (since R_B(a)≠0).
The two distinct nonzero roots force different v. Put W=Q/X≠0.
We can choose α,β,λ solving L+βR_B−αR_A=λW iff W is outside
span(R_A,R_B): if outside its image is a basis of the quotient
line; if inside it cannot reproduce the nonzero class [L].
This is an exact obstruction, not merely a sufficient rank test.

## Quadratic lower bound
For each pair A regard [R_A] as a point of PG(2,q). Unless [R_A]=[W],
it determines one of q+1 projective lines through [W]. If W has two
site roots, then it is proportional to R_A for their pair, which
contradicts the disjoint-pair criterion with any pair B off A, as n≥4.
Thus W has z∈{0,1} site roots.

For pairs not involving site roots of W, their projective lines
through [W] are distinct. If distinct pairs A,B with the same line
are disjoint, contradiction by the criterion. If they intersect in
a site a, both R_A,R_B vanish at a, so every polynomial on their line
including W vanishes there, also a contradiction. If W has a site
root a, the line of polynomials vanishing at a is reserved: it contains
[W] and no pair point off a. Counting available lines gives
binom(n−z,2)≤q+1−z. This implies both stated inequalities.

## Explicit matching upper and arbitrary tight two-epoch budgets
Take F=F_(s²), S⊂F_s^*, θ∈F\F_s and Q=X+θ X². For disjoint A,B over
F_s, span_F(R_A,R_B) is the extension of a two-dimensional F_s space.
Were it to contain W=1+θX, applying the basis-coordinate maps of F
over F_s would put both 1 and X in the same base span. But the
degree≤1 part of this particular span is one-dimensional since both
R_A,R_B are monic quadratics. Contradiction. Taking s a power of two
between n+1 and 2(n+1) gives field size <4(n+1)² for every n; this
construction needs no odd characteristic.

More generally for two epochs with positive a,b, a+b=t+1 and one
fresh scalar, put m=min(a,b). Choose n distinct nonzero sites in
F_s and use a degree-m extension with basis 1,θ,…,θ^(m−1) and
Q=Σ_(j=1..m) θ^(j−1) X^j. Spend the refresh on the smaller
read set in the view algebra: if that epoch is first, parametrize by
the final polynomial, independent uniform with the same secret and
independent of λ (translation conditional on λ), and use −λQ before.
For an overlapping view, at most t distinct total roots suffice
with λ=0. For disjoint sets the t+1 rows of the common degree-t
zero-constant Vandermonde have rank t and any t rows are independent,
since all sites are nonzero and distinct. The unique cokernel
linear functional over F_s therefore has all coordinates nonzero.
Restricted to the m refresh rows, it is a nonzero row vector. The
m columns of X through X^m evaluate as an invertible zero-constant
Vandermonde on those m sites, so at least one has nonzero pairing.
The extension basis guarantees the pairing with the masked refresh
column Q is nonzero. Thus the added one coin fills the cokernel for
every disjoint view, explicitly giving field size s^m. No claim of
matching lower bound for larger m.

## Prior work and limits
Shamir, *How to Share a Secret*, https://doi.org/10.1145/359168.359176 .
Almeida–Napp–Pinto, *A new class of superregular matrices and MDP
convolutional codes*, https://arxiv.org/abs/1303.3807 ; Hutchinson–
Smarandache–Trumpf, *Superregular Matrices and the Construction
of Convolutional Codes having a Maximum Distance Profile*,
https://arxiv.org/abs/cs/0607089 ; and Almeida–Napp, *Superregular
matrices over small finite fields*, https://arxiv.org/abs/2008.00215 .
These impose stronger structured simultaneous-minor conditions on
different matrices. The present lower uses an exact obstruction in
the Shamir/one-direction model and finite projective counting; the
basis extension avoids requiring general superregularity. This is an
initial primary-source comparison, not priority established or a
general multi-epoch/small-field solution.

The geometric language is a pencil of lines through [W], or projection
from that point. The forbidden secants here are exactly those joining
points labeled by disjoint root pairs, not all secants of a conic. The
line count can also be seen directly: quotient by the line of W to get
a two-dimensional vector space, whose nonzero vectors partition into
(q²−1)/(q−1)=q+1 one-dimensional spaces. See Hirschfeld,
*Projective Geometries over Finite Fields*, "First properties of the plane,"
https://academic.oup.com/book/53387/chapter-abstract/422057584 .


## What was checked

Two pinned Lean 4.34.1 files, SmallField.lean and QuadraticRefresh.lean,
check the disjoint-pair offset and the extension-field secant algebra.
The full projective count, channel reduction, and general extension
argument are written proofs, not whole Lean theorems. Independent exact
scans checked 86,448 affine-rank cases, 2,163 explicit extension cases,
90,661 Sidon classifications and 4,599 small cyclic difference controls.

Run python3 checks.py and python3 sidon_checks.py to repeat the scans.
The Lean files use Mathlib commit d13f23b723b8a846827a245b89c10fc7d3f11612.
