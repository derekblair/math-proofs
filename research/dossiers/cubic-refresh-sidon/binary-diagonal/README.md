# Exact randomness and field-size tradeoff for binary Shamir refresh at n=2m

## Model and results

Let F=F_(2^r), n=2m (m≥2), and let S be any n distinct nonzero sites,
so necessarily 2^r≥2m+1. A degree≤2m−1 Shamir polynomial with uniform
independent initial nonconstant coefficients holds its fixed secret.
A boundary adds a random degree≤2m−1 polynomial whose constant is zero.
The removed epoch state and refresh coins are not available. A passive
observer reads up to m current sites in each of the two epochs.
The refresh is independent of the initial polynomial and secret. We
only count its independent fresh randomness, not initial sharing,
distribution or protected erasure work.

If m is even:
- With d independent uniform F-valued coins in fixed public F-linear
  refresh directions, exact privacy is possible iff rd≥m. Equivalently,
  the minimum number of field coins is ceil(m/r).
- With k independent unbiased bits in fixed public binary-linear
  refresh directions (their field-valued coefficients are arbitrary),
  exact privacy is possible iff k≥max(m,r). This can beat the previous
  restricted model's bit count r ceil(m/r), with no fractional draws.
- The minimum field size with just one field scalar is
  2^(max(m,ceil(log2(2m+1)))). It is 2^m for all even m≥4 and 8 for m=2.

If m is odd, one field scalar (or r independent bits) suffices over every
field meeting the sites bound, since a constant unit weight sequence
has zero sum over 2m sites but nonzero sum over each odd m-set. Contrast
fields of characteristic not dividing m, where the prior diagonal
construction works with one scalar and every valid roster, and in
particular q=2m+1 whenever that is a prime power. The exponential field
penalty for one scalar in the binary even case is exact, not merely a
generic large-field effect.

## Reduction to a weighted balanced-subset problem

Write R(X)=∏_(a∈S)(X−a) and write the refresh polynomial as XW(X),
deg W≤2m−2. Such W are in bijection with zero-sum field-valued weights
v(a)=W(a)/R'(a): the inverse is
  W(X)=Σ_(a∈S) v(a) R(X)/(X−a).
The degree 2m−1 coefficient equals Σ_S v, and evaluations at sites
give the asserted labels by Lagrange interpolation. The distinct
sites ensure R'(a)≠0.

If the two full read sets overlap there are at most 2m−1 distinct sites,
and initial uniform polynomial coefficients alone perfectly mask
the secret, regardless of independent refresh. If they are disjoint,
they are complements A,B; the one remaining coordinate after
quotienting the initial nonconstant evaluation span is a scalar
whose refresh component is, up to a nonzero multiple,
  Ψ_A(W)=Σ_(a∈A) v(a).
Indeed the common initial coefficient-space evaluation at the 2m sites
has one-dimensional cokernel, whose weights at a are 1/(a R'(a)).
These annihilate each column X^j, 1≤j≤2m−1, by the top-Lagrange-
coefficient identity applied to X^(j−1); any 2m−1 evaluation rows
are independent. The secret coefficient in this quotient is nonzero:
if the all-one evaluation vector were in the common initial span then
some degree≤2m−1 polynomial with zero constant would equal 1 on
2m distinct sites, making it identically 1, contradiction. Refresh
adds aX-normalized row only in B, giving Ψ_B, which equals −Ψ_A.
The other view coordinates are a full uniform mask conditional on
refresh, so perfect privacy holds iff Ψ_A(W) is uniform on F for every
m-set A. This equivalence holds for any independent refresh
distribution. Fixed-length classically adaptive reads are handled by
the unnormalized fixed-path argument. No coherent access, side-channel
leakage, active adversary, or threshold implementation is modeled.

## Whole field coins: a forbidden-weight kernel

For d directions let v_i(a) be their zero-sum weights, and write
h_a=(v_i(a))_(i≤d) in F^d. Then Ψ_A for independent uniform field
coins is uniform on F iff Σ_A h_a≠0. As an additive vector space
F^d has binary dimension rd. Treat its site weights as the columns
of a binary parity-check matrix H (at most rd independent rows).
Its binary kernel C contains the all-one vector and has no word of
weight m. The converse also holds: choose any such H with ≤rd rows,
pack binary coordinates into F^d (padding by zero if needed), and
independently interpolate each direction to obtain exactly the
required uniform projection behavior.

For m even, n=2m=4t with t=m/2. The primary theorem of Hikoe Enomoto,
Peter Frankl, Noboru Ito and Kazumasa Nomura, *Codes with given
distances*, Graphs and Combinatorics 3 (1987), 25–38,
https://doi.org/10.1007/BF01788526 , proves every binary linear code
of length 4t and dimension greater than 2t has a word of weight 2t.
Applying it to C yields n−rank(H)≤m, hence rd≥rank(H)≥m. In contrast
Frankl–Rödl's forbidden-distance result for general nonlinear codes
would provide only r d=Ω(n); that result is not needed here.

For the upper, choose m−1 zero columns followed by the m standard
basis columns and their sum in the binary m-space. The total sum is
zero, and the only nonempty dependency among the m+1 nonzero columns
is their full set. Every m-set of sites selects at least one and at
most m of these m+1 columns, yielding nonzero sum. The resulting
kernel consists of freely chosen m−1 bits and a repetition block of
length m+1. Pack these columns whenever rd≥m. Use at most d coins;
if exactly d linearly independent nonzero directions are desired
and d≤2m−1, extend the obtained span, which cannot hurt privacy.
Zero-weight columns here are permitted: they do not reveal a
secret when the disjoint balanced-view criterion holds.

## Exact bit-linear refresh without field padding

Suppose refresh is a fixed F_2-linear (or affine) function of k independent bits.
For each m-set A its quotient map from F_2^k to F must be surjective
because its output must be uniform. This gives k≥r. Fix a nonzero
F_2-linear output bit ℓ:F→F_2 (e.g. a nonzero coordinate functional).
For each bit direction i form parity-check column
(ℓ(v_i(a)))_i∈F_2^k. Their total is zero. Every balanced A has nonzero
sum of these columns, since the corresponding scalar output bit
must be a nonzero linear functional of the k seed bits (surjective
F-valued output cannot have zero image under ℓ). The same known
forbidden-weight theorem gives k≥m when m is even.

To attain k=m if r≤m, use an auxiliary field K=F_(2^m). Interpret
the m-bit witness columns above as w_a∈K. Choose z uniform in K
(m independent bits), and fix any surjective binary-linear map
π:K→F (no subfield embedding or field homomorphism required).
Set v_z(a)=π(z w_a). Their sum is zero and the resulting W_z by
interpolation is binary-linear in z. For any balanced A,
  Ψ_A(W_z)=π(z⋅Σ_A w_a),
uniform in F because Σ_A w_a≠0 and multiplication by it permutes K.
If r≥m, the one-field-coin construction uses r bits. This is an
exact bit-seed minimum for the binary-linear independent-bit
interface, not a claim of minimum Shannon entropy over arbitrary
nonlinear or nonuniform refresh distributions.

## Source boundary

The exact coding lower is prior; the contribution here is the
model reduction, matching constructive interpolation and tight
field-scalar versus bit-linear randomness consequences. Frankl and
Rödl's original general theorem is *Forbidden intersections*,
Trans. AMS 300 (1987), 259–286; for a primary modern proof/extension
see Keevash and Long, https://doi.org/10.1090/tran/7015 .
Standard proactive sharing literature, e.g. Herzberg–Jarecki–
Krawczyk–Yung, https://doi.org/10.1007/3-540-44750-4_27 ,
addresses distributed refreshing with different constraints; no
priority for the coding extremum or production KEM is asserted.

Concrete examples: at n=12,m=6 over F_16, two whole-field coins
are necessary and sufficient (eight bits), whereas six independent
bits with binary-linear refresh suffice and are necessary. At n=16,m=8
over F_32 the corresponding counts are ten vs eight bits. At the
minimal possible field r=ceil(log2(2m+1)), unrestricted bit-linear
refresh uses exactly m bits for even m≥4.

## Verification boundary

The pinned Lean 4.34.1 file BinarySyndromeBits.lean checks the bitwise
basis-plus-sum dependency lemma. It does not formalize the imported
coding bound, interpolation, or the privacy model. Independent exact
replay checks 18,568 subset/seed-rank cases and 100 full affine view ranks.
Run python3 checks.py from this directory to reproduce those checks.
