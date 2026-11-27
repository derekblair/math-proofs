# Anchored exact nonlinear refresh from unordered circuits

## Setting

Use the prior two-epoch diagonal model with n=2m distinct nonzero sites
in F_q, q=2^r≥n+1, degree≤2m−1 Shamir, and an independent zero-constant
refresh. This models only passive current-share reads of up to m per
epoch and hidden refresh; no deployment or KEM. By the Lagrange
normalization v(a)=W(a)/R'(a), where refresh polynomial is XW and
R(X)=∏_(a∈S)(X−a), it suffices and is necessary that v sum to zero
and every balanced m-subset's syndrome Σ_A v be uniform F_q.
The remainder assumes 1≤r≤m−1. If r≥m, the prior one-field-scalar
construction already uses only r bits for the even-m case.

## Exact distribution with unordered support sites

Fix a distinguished site d. Choose a uniformly random r-set T from
the remaining n−1 sites; canonical public site order assigns a fixed
binary basis of F_q across T. At d put the sum of all basis vectors,
and elsewhere put zero. The r+1 nonzero columns indexed by B=T∪{d}
have only one nonempty zero-sum subset: B itself. Thus a balanced
view A has zero syndrome exactly when B is monochromatic for its
cut. Since B contains d, monochromatic means precisely T is contained
in the m−1 other sites of the side containing d. Consequently the
zero probability is the same for all A and equals
  Z = binom(m−1,r) / binom(n−1,r)
    = 2 binom(m,r+1) / binom(n,r+1) < 2^(−r)=1/q.
The strict inequality holds term by term in the falling-factorial
ratio for r≥1. Draw a uniform independent U in F_q^* and multiply
every weight by U. Conditional on the unscaled syndrome being
nonzero, multiplication makes the scaled value uniform over F_q^*,
regardless of the distribution of the unscaled nonzero value.

Finally output the all-zero vector with probability
  α=(1/q−Z)/(1−Z),
and with probability 1−α use the scaled circuit above.
Every balanced view has zero probability α+(1−α)Z=1/q and each
nonzero probability (1−α)(1−Z)/(q−1)=1/q. This proves exact privacy.
An equal-in-size binomial ratio is a rational number, so the complete
distribution can be sampled exactly with variable-length fair bits.
This does not assert that the same distribution comes from a fixed
length fair-bit seed, because its denominators need not divide powers
of two.

For fixed T the mapping U↦scaled weights is injective (inspect any
of the nonzero basis labels), and different T have different nonzero
supports. Hence its exact Shannon entropy is
  h₂(α)+(1−α)(log₂ binom(n−1,r)+log₂(q−1)).
For r=Θ(log n), this is
  r log₂ n − log₂(r!) + r + o(1).
Indeed log₂ binom(n−1,r)=r log₂ n−log₂(r!)+O(r²/n);
each factor of Z divided by 2^(−r) is
1−(j+1)/(n−1−j), j=0,...,r−1, so α=O(r²/(nq)). The
entropy saving versus the ordered independent site sampler is
log₂(r!)−r+o(1)=Θ(r log r) in this regime, an additive rather
than a leading-order improvement. Take the best of this and
previous upper bounds for small or different parameters.

## Fixed-anchor exactness forces every r-set

For any distribution on anchored (r+1)-site circuits of the same kind,
scaled by an independent uniform F_q^* and optionally mixed with a
fixed probability of zero, the zero syndrome event still depends
only on the support. Exactness means that
  Σ_(T⊆A', |T|=r) p_T
is constant over every (m−1)-set A' of the n−1 non-anchor sites.
Here A' can be arbitrary because A=A'∪{d}. The containment
incidence matrix with rows indexed by (m−1)-sets, columns indexed by
r-sets, has full column rank over R when r≤min(m−1,n−m)=m−1
(Gottlieb's primary theorem). The uniform distribution already
solves the equation and the constant is forced by averaging.
Therefore the distribution on support T must be uniform; no
sparser weighted support design can improve the anchored model.
This does not imply the same for unanchored circuit designs,
non-circuit refresh directions, or alternative scalar randomization.

The short incidence-rank result used here is D. H. Gottlieb,
*A certain class of incidence matrices* (1966),
https://www.math.purdue.edu/~gottlieb/Bibliography/Incidence.pdf.
No priority claim for the rank theorem or a generic refresh.
The arbitrary nonlinear O(log n) exact construction at q≈n remains
open here. The contribution is exact unordered anchored sampling,
its entropy comparison, and the exact no-sparser-anchor consequence.

## Stronger arbitrary-sampler entropy lower bound

For even m, put k=ceil(m/r), c=1/q. The simultaneous-collision argument
in the prior nonlinear dossier shows the sum of the k largest output
masses is at most c, without any assumption on the sampler. This actually
implies the collision entropy, and hence the Shannon entropy, is at least
log₂(qk). Here is the elementary refinement.

Order output masses p₁≥p₂≥…, let y=p_k and P=Σ_(i≤k)p_i, and set
x=P−(k−1)y≥y. For fixed P,y the first k squares have sum at most
x²+(k−1)y²: write their excesses over y as nonnegative, whose sum
of squares is at most the square of their sum. All later masses
are ≤y, so
  Σ_i p_i² ≤ x²+(1−x)y.
The right side is increasing in x≥y, so replace x by c−(k−1)y.
The resulting expression is convex in y on [0,c/k] and its endpoint
values are c² and c/k. Since k≤q, c²≤c/k. Therefore Σ_i p_i²≤1/(qk).
Jensen's inequality for −log gives H(p)≥−log₂ Σ_i p_i²≥log₂(qk).
In particular, arbitrary samplers at r=m−1 (where site capacity permits)
need exactly m bits of entropy, by matching the earlier bit-linear
construction; for r≥m the optimum is exactly r. In the target r≈log n
regime this is still only order log n, not a log² lower bound.

## A limitation of few-mode field-linear mixtures

For clarity, a mode here means a chosen affine space of zero-sum
weighted vectors with F_q dimension at most d, followed by a
conditionally uniform draw from that space. For a balanced view A,
each mode projects to either uniform F_q or one point. In an exact
sampler the weighted point-mass portion, if nonzero, must itself
give the uniform law after normalization, since the other portion is
uniform. Thus any view that kills one mode must kill at least q modes,
and no mixture with fewer than q modes can help when rd<m (every
individual d-dimensional mode has a bad balanced view in that regime).

More generally, if h is any positive integer with
r((d+1)h−1)<m, any h modes collapse in the same view to the same
point: apply the Enomoto–Frankl–Ito–Nomura theorem to binary rows
encoding each mode's basis directions and the differences of its
affine offsets relative to one reference. That gives at most
r((d+1)h−1)<m rows, hence a balanced annihilator. The h mode
masses total at most 1/q; averaging implies at least qh modes
(assuming fewer than h is impossible by the same argument).
This bound concerns the discrete mode representation, not an
extra entropy charge for the underlying sampler. It does not
rule out useful high-mode mixtures.
