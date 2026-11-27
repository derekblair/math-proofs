# Nonlinear exact refresh sampling beats any bit-linear sampler

## Setup

Use degree≤2m−1 Shamir, n=2m distinct nonzero sites S in F_q,
q=2^r≥n+1, with a uniform initial nonconstant polynomial. A boundary
adds a random degree≤2m−1 zero-constant polynomial independent of
the initial sharing and of its secret. Old state and sampler coins
are unavailable. The passive observer reads at most m current
sites per epoch; no malicious behavior, erasure implementation,
coherent query, or production security claim.

As in the earlier diagonal reduction, write a refresh as XW and its
weighted evaluations as v(a)=W(a)/R'(a), R(X)=∏_(a∈S)(X−a).
This is a bijection between degree≤2m−2 W and weight vectors with
Σ_S v=0, using the explicit Lagrange formula
W=Σ_(a∈S) v(a) R/(X−a). For disjoint full read sets, the quotient
of the initial uniform mask span is one-dimensional; the refresh
component is Σ_(a∈A) v(a), up to a fixed nonzero factor. The secret
shift in that quotient is also nonzero, since no zero-constant
degree≤2m−1 polynomial equals 1 on all 2m nonzero sites. Ordinary
privacy against every fixed secret requires and suffices that the
weighted sum on each m-set A be exactly uniform in F_q. Overlapping
full reads have at most 2m−1 distinct sites and already hide the
secret when conditioning on the independent refresh. Padding
shorter views and evaluating adaptive path probabilities extends
this to classical adaptive reads. The sampler need not be linear.

## Exact upper: one site sample per field basis bit

Fix one site d and one binary basis (u_1,...,u_r) of F_q.
Independently sample J_i uniformly in S. Set binary bit-i weights
to the vector e_(J_i)+e_d (equal indices cancel). Combine the bit
weights in the field basis. Each binary vector has coordinate sum
zero, hence the full field weight vector also has sum zero. For
every balanced A, bit i of its weighted sum is
  1[J_i∈A] xor 1[d∈A].
It is exactly fair because |A|=n/2, regardless of d's membership
in A, and the bits are mutually independent because the J_i are
independent. Therefore the sum is exactly uniform in F_q.

The space of n^r site tuples is uniform. The map to weighted
vectors is injective: in each basis bit, zero means J_i=d, and
otherwise the non-d support site uniquely specifies J_i. The
Lagrange map is also bijective, hence both the output refresh
entropy and the site-tuple source entropy are exactly r log₂ n.
If n is a power of two, this is an exact fixed fair-bit cost.
Otherwise exact uniform rejection sampling on n or on n^r
outcomes gives finite expected fair-bit cost, e.g. <2 ceil(r log₂ n)
by drawing a binary integer and rejecting above the range. One
must not claim a fixed fair-bit seed realizes this particular
n^r-uniform distribution when n is not a power of two.
An equal J_i=d is essential to the fairness count; excluding it
would bias the bit.

For even m and r≈log₂ n, this gives O(log² n) fresh entropy, versus
the exact Ω(n) cost in the fixed binary-linear independent-bit
interface. The latter is a restriction on the map from bits to
polynomial, not a lower bound on arbitrary sampling. At n=256
and minimal q=512, for example, this construction uses exactly
72 fresh bits, versus 128 for every binary-linear bit sampler.
For small n or very large r the earlier binary-linear sampler
may be cheaper, so take the minimum upper bound when comparing.

## Arbitrary-sampler lower bound via simultaneous collisions

Assume m even. Let k=ceil(m/r). Fix **any** k distinct outcomes
of the refresh distribution (if fewer exist, take all outcomes).
Each outcome gives a zero-sum weight vector in F_q^S. Subtract
one reference outcome from each other one and interpret binary
coordinates of the k−1 difference vectors as rows of a parity
check matrix. This has at most (k−1)r<m rows, no restrictions on
the sampler that produced those outcomes, and its columns are
indexed by the n sites. The binary kernel therefore has dimension
greater than m and contains the all-one vector. By the primary
Enomoto–Frankl–Ito–Nomura forbidden-weight theorem, every binary
linear code of length 4t and dimension >2t has a word of weight
2t. Here n=4t with t=m/2; it supplies an m-set A annihilating
every difference. Thus the chosen outcomes all map to the same
syndrome in F_q for this A.

Uniformity of that syndrome bounds total probability of any k
outcomes by 1/q. In particular fewer than k outcomes are impossible
(the entire probability would then share one syndrome). The mean
of the k largest atom masses is at least the overall mean, hence
support cardinality is at least qk. Thus any exact fixed fair-bit
sampler needs at least ceil(log₂(qk)) bits. For a general sampler,
with p_top the probability mass of its k heaviest atoms, the atoms
within that set are at most 1/q, and all other atoms are at most
1/(qk). Shannon entropy (base two) therefore obeys
  H ≥ p_top log₂ q + (1−p_top) log₂(qk)
    ≥ r + (1−1/q) log₂ k.
The same bound applies to the generating independent seed entropy
by deterministic data processing. For q roughly n, this is at
least 2 log₂ n−log₂ log₂ n−O(1), still short of the known upper.
Using just one common site draw with no extra randomness has
support only n<qk and is therefore insufficient. More general
correlated site draws are not ruled out.

## What is not proved; closest primary background

Exact O(log n) randomness at q≈n remains open here. A small-bias
space over the r(n−1) binary coordinates of zero-sum weights can
give *approximate* uniformity in all balanced quotient views:
if each nonzero binary linear character has bias ≤ε, Parseval
and Cauchy–Schwarz bound total variation of any such projection
to uniform by (1/2)√(q−1) ε. This would not prove exact privacy
and is not offered as equivalent. Naor–Naor's small-bias spaces
https://doi.org/10.1137/0222053 are primary background for that
distinction. Alon–Bergmann–Coppersmith–Odlyzko's balancing sets
https://www-users.cse.umn.edu/~odlyzko/doc/arch/balancing.vectors.pdf
concern covering an input by some balancing operation; our
requirement is exact uniform distribution of every balanced
subset sum, not existential balance of each word. The coding
theorem used in the lower is explicitly prior: Hikoe Enomoto,
Peter Frankl, Noboru Ito and Kazumasa Nomura,
*Codes with given distances* (1987), https://doi.org/10.1007/BF01788526.
The claims here are a scoped exact construction and arbitrary
sampler support/entropy bounds, not a new KEM or priority assertion.

## Correlating only the one-hot site draws does not save the asymptotic entropy

Restrict to the construction form v_i=e_(J_i)+e_d in a fixed binary basis,
but allow an arbitrary joint law of J=(J_1,...,J_r), independent of the
secret. For exact privacy, membership bits 1[J_i∈A] must be jointly
uniform for every balanced A (the possible fixed d flip is immaterial).
For 1≤r≤n/4, this forces
  H(J) ≥ (1−binom(r,2)/n)_+
          [r log₂ n−2 log₂(r!)−2r]_+ .
The positive part on the first factor is unnecessary when binom(r,2)≤n.
Consequently when r=O(log n), the leading entropy r log₂ n of independent
site draws cannot be improved in this architecture. This is NOT a
lower bound of that magnitude for arbitrary nonlinear refreshes.

### Pairwise collision normal form

Each draw's marginal is uniform on S: balanced subset probabilities
are always 1/2, so swapping one included site and one excluded site
equates their marginal masses. For any pair of draws, write
s_ij=P(J_1=i,J_2=j)+P(J_1=j,J_2=i) for i≠j. In
P(J_1,J_2 both in A)=1/4, four-point switching on two swapped
positions at a time cancels diagonals and all contributions from a
common base, proving
s_ij+s_kl=s_ik+s_jl=s_il+s_jk
for any four distinct sites. Choose initial parameters a_1,a_2,a_3
solving s_ij=a_i+a_j on their triangle. For i≥4 set a_i=s_1i−a_1;
the identities on {1,2,3,i} give s_2i and s_3i as needed, and
those on {1,2,i,j} give the remaining s_ij. Thus all offdiagonal
symmetrized masses are additive in these site parameters. A balanced
cut has crossing mass exactly 1/2, hence m Σ_i a_i=1/2 and Σ_i a_i=1/n.
Total offdiagonal mass is (n−1)Σ_i a_i=1−1/n, so P(J_1=J_2)=1/n.
In addition row sum of the s_ij is at most 2/n from the two uniform
marginals, giving (n−2)a_i+1/n≤2/n; thus each ordered offdiagonal
atom is ≤2/[n(n−2)]. This pair result by itself does not tensorize.

### Higher-order switching proof

For t≤r, define B_t as the largest probability, over any t indexed
draws and fixed t-element set T, that their unordered support is T
(hence all t are distinct). Let B_0=1. To bound B_t, put T={x_1,...,x_t}
and choose distinct y_i outside T. Hold a base of size m−t outside
the 2t displayed sites; this is possible since n−2t≥m−t for t≤m. For each of the 2^t choices of one site from
each pair (x_i,y_i), append those choices to the base to form a
balanced A. The probability that all t chosen draws fall in A is
2^(−t) for each A. In their alternating sum, a tuple cancels if it
uses neither element of some pair, and cannot contribute if it uses
both elements of a pair. The surviving tuples use exactly one from
every pair and none from the base. Hence, writing p_T for the
exact-support probability of these t indexed draws,
  p_T ≤ Σ_(I⊂[t], |I| odd) p_{T with x_i replaced by y_i for i∈I}.
This follows by dropping all other nonnegative even-sign terms.

Now average over a uniform injective choice of y_1,...,y_t outside T.
For |I|=s the inserted sites form a uniform s-subset of the complement
of T, so the expected replacement mass is at most the probability
that the support contains the t−s retained sites, divided by
binom(n−t,s). The containment probability is at most binom(t,s)B_(t−s)
by a union over possible indexed coordinates witnessing those distinct
retained sites. Summing the binom(t,s) choices of I gives
  B_t ≤ Σ_(s odd) binom(t,s)^2 B_(t−s) / binom(n−t,s).
For n≥4t, binom(n−t,s)≥(n/2)^s/s! for s≤t. Induction proves
B_t≤4^t(t!)²/n^t: substitute that bound on B_(t−s), divide
through by 4^t(t!)²/n^t, and the remaining sum is at most
Σ_(s odd≥1) (1/2)^s/s!<1 (even the geometric sum over all
positive s is 1). By the pair result and union bound the probability
all r draws are distinct is ≥1−binom(r,2)/n. Every ordered distinct
tuple atom is bounded by the unordered mass B_r. Its contribution
to Shannon entropy is therefore at least its mass times
[r log₂ n−2 log₂(r!)−2r]_+. This proves the bound. The refresh
map remains injective on tuples even when draws are correlated,
so the same bound is on output entropy in this architecture.

## Verification boundary

The pinned Lean 4.34.1 file SelectorFair.lean checks exact balance
of the per-bit membership test, including the fixed-site XOR. It does not
formalize the Shamir privacy reduction, the entropy inequalities or the
full switching argument. Independent replay checks 192 balanced-syndrome
histograms, six complete affine view distributions, 120 simultaneous
collisions, and four correlated pair laws plus the induction constants.
Run python3 checks.py from this directory. This is an ideal refresh
result, not an implementation, deployment or new encryption primitive.
