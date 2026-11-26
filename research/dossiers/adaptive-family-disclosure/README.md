# Oracle-free adaptive disclosure with a polynomial-size replicated witness design

## Model and claim

One honestly generated challenge envelope for one secret in the XOR group G=(F₂)^ℓ, with ℓ the component KEM key length. A different group needs an explicit exactly uniform group-mask encoding. There are n endpoint
domains and r labeled KEM families. For each participating (family, endpoint)
pair the keys are independently generated under its family's algorithm;
encapsulation randomness is also independent. Setup-time disclosures are also
permitted under those same total budgets; count them from the start. Algorithms and the public roster
are fixed, and all components of the challenge public view are classical. A QPT
observer can adaptively request up to c entire endpoint domains and up to r−1
entire families. Both request types and responses are classical. Each disclosure
reveals corresponding receiver private keys, and may return outputs of specified efficient local computations on those keys and the public challenge envelope. This does not include other local state or unbounded computation oracles. The challenge is
between two classical messages selected after public setup and before the
envelope is generated. No sender coins, cross-domain correlated state,
unauthorized decapsulation service, malformed-envelope handling, eventual
aggregate recipient, or reconstruction transcript is included. Correctness,
separately, must tolerate up to f offline endpoint domains; family disclosure
is not a family outage.

Fix a public B-block set system on the n endpoints in each family. Each block
has k=f+1 distinct endpoints, and each c-set misses at least one block (assume
c+k≤n). Sample an array of rB block values uniformly subject to their sum being
the secret. In each family place a copy of that block value under the KEM-derived
mask at each block member. For elementary masks use G=(F₂)^ℓ and XOR directly
with an independently encapsulated ℓ-bit key per incidence. Any f outages
leave one copy of every block, so recovery succeeds except base correctness
errors (union bound on the number of copies used). Let ε_i bound the
single-challenge post-quantum real-vs-random KEM key advantage with no decapsulation
oracle. Message distinguishing advantage is at most
2 B k Σ_i ε_i (or 2 r B k max_i ε_i), counting differences in acceptance
probabilities. The component advantage ε_i is measured at the reduction runtime, which is polynomial in the adversary runtime, explicit incidence roster and base operations. Apply this as a polynomial-loss security guarantee only when the explicit roster and those algorithms are polynomial in the security parameter. Alternative per-family block counts and sizes use
2 Σ_i Σ_block |block| ε_i.

## Proof of the adaptive reduction

Fix a total order of family/block pairs. Every complete legal transcript has
a witness: a family whose full disclosure was never requested and a block in
that family whose endpoint members were never disclosed. This holds pointwise,
not just with some probability. Define a pair's restricted acceptance event as
acceptance and that pair being the first such witness. Its contribution equals
the acceptance probability of an experiment which aborts with zero upon any
disclosure ruling that pair out, then checks at completion whether it was first.
This equality is valid without conditioning on survival. Classical request
labels allow ordinary straight-line abort, preserving the QPT state of every
non-aborted execution. No rewinding or measurement of internal adversary state.

For a fixed witness pair and fixed message bit, hybridize each of its k key
masks to independent uniform, paying at most k ε_i. A base reduction inserts
the challenge public key before the adversary chooses its two messages and only
needs the challenge encapsulation after message selection. Other encap runs at
the same public key are public algorithms and can be done locally. The inserted
secret key is not needed on any branch contributing to the restricted event.
On attempted disclosure that would require it the reduction aborts with zero,
consistent with the definition of the event. No assumption on the probability
of this abort is used.

With these masks uniform, the two restricted experiments have identical laws.
Couple their share arrays by shifting solely the witness block value by the
difference in messages; this is a bijection between uniform additive fibers.
Couple each independent uniform witness mask by the same shift (XOR), so all
classical challenge ciphertext material is identical in the two worlds.
Every disclosure on a surviving branch is identical, since that branch
reveals no witness mask. Conditioning on common setup, message pair, and
coupled coins, identical classical interactions preserve identical adversary
state and behavior, including classically adaptive requests and final witness
selection. The equal laws also follow inductively for unnormalized branch
states. Two hybrid legs per witness and summing the disjoint restricted
acceptance events proves the stated bound.

Optional bandwidth tradeoff: use one KEM key per participating endpoint/family
and expand it to the exact public number of incidence masks with a
post-quantum PRG (quantum-computational output indistinguishability, classical
output, bounded stretch polynomial in the explicit roster). For a chosen
witness hybridize the k entire participating endpoint masks via KEM then PRG,
paying k(ε_i+ε_G). These endpoints are never disclosed on contributing branches.
The shifted coupling can now adjust only selected independent uniform
coordinates after this hybrid. This lowers the number of encapsulations to
the total number of participating (family, endpoint) pairs, not the number of
masked group elements. Both versions exclude disclosure of sender state,
derived secret logs at other endpoints, and active security services.

## Cost, coverage, and a sharp architecture barrier

For k=f+1 and c+k≤n let
p=binom(n−c,k)/binom(n,k)=binom(n−k,c)/binom(n,c).
Each block misses exactly binom(n−k,c) different c-sets. Double counting
therefore gives B≥ceil(1/p); B≥c+1 also, since one representative per block
hits all when B≤c. For c>0 the standard covering-design relation is exact:
the minimum B is the covering number C(n,n−k,c) for complements; c=0 needs
one block. Independently uniform random k-sets leave a fixed c-set uncovered
with probability (1−p)^B≤exp(−pB); B=floor(log binom(n,c)/p)+1 suffices by a
union bound. This is an existence bound, and does not claim efficient
certification of an arbitrary public roster. Efficient explicit options:
- n≥(c+1)(f+1): use c+1 disjoint blocks, minimum possible block/copy count
  within this construction. Direct bound ≤2r(c+1)(f+1) max ε_i, even when
  both c and f grow. Copy count grows by factor (c+1)(f+1)/(c+f+1) relative
  to the leaner Shamir separated layout. This is proof-vs-size tradeoff,
  not measured performance or a lower bound for general adaptive envelopes.
- Cluster interpolation: partition into g disjoint clusters of sizes
  s_j≥k and include all k-subsets inside each. Avoiding all missed blocks in a
  cluster requires a hit on at least s_j−f endpoints (equivalently its
  complement has at most f endpoints). Additivity across disjoint clusters
  gives exact transversal number n−gf and B=Σ_j binom(s_j,k). Thus choose
  g≤min(floor(n/k),floor((n−c−1)/f)) for f>0. For fixed g, balanced sizes
  minimize B: moving one site from a cluster of size a to one of size b<a−1
  changes the sum by binom(b,k−1)−binom(a−1,k−1)≤0 (Pascal's identity).
  Take the largest admissible g and balance. For fixed f and constant
  fractional slack n−c−1≥δn>0 this gives g=Ω(n), bounded cluster size, and
  B=O(n), with constants depending on f,δ. For f=0 the singleton construction
  suffices. No optimality claim among non-cluster covers.
- Fixed f: use all k-sets on exactly c+f+1 endpoints. B=binom(c+f+1,f+1)
  is polynomial; with PRG bundling per family uses exactly c+f+1 KEMs,
  though the incidence payload and reduction take a larger polynomial.
  Fixed c is also polynomial (constant-width enumeration of complementary
  c-sets suffices on c+k endpoints).
- At n=c+k the complement of a c-set is the only possible block avoiding
  it. Thus B=binom(n,k) is forced for this particular replicated design
  regardless of KEM assumptions; when c,k are both fixed positive fractions
  of n it is exponential. This does not rule out efficient adaptive Shamir,
  noncommitting primitives, computational sharing, or architectures beyond
  one shifted replicated block.
- More generally if min(c,k) is linear in n, p≤(1−c/n)^k is exponentially
  small. For max(c,k)≤n/2 with c+k not too close to n, use the exact product
  p=Π_{j<k}(1−c/(n−j)) to check whether the probabilistic upper bound is
  useful. No general claim for near-cut parameters.

## Prior work and scope

This is a receiver selective-opening flavor but only a specific
message-indistinguishability game with special additive correlation and no
oracle; it is not general RSO semantic simulation, IND-RSO for arbitrary
correlated message distributions, or a threshold implementation of ML-KEM.
The replicated sharing itself is classical cumulative-array/general access
structure sharing. The result here is the explicit witness-indexed adaptive
reduction and resource comparison for the family/endpoint envelope; no claim
it precedes all related reductions, that it is a new KEM, or that it
improves complete deployed systems.

- Benaloh and Leichter, Generalized Secret Sharing and Monotone Functions:
  https://www.cs.umd.edu/~gasarch/TOPICS/secretsharing/monotone.pdf
- Bellare, Dowsley, Waters and Yilek, Standard Security Does Not Imply
  Security Against Selective-Opening (simulation-based receiver separation
  does not contradict the restricted game):
  https://cseweb.ucsd.edu/~rdowsley/pdf/BDWY12.pdf
- Hofheinz/Rupp, separation and equivalence (care with definition):
  https://people.inf.ethz.ch/dhofheinz/pdf/conf/tcc/HofheinzR14.pdf
- Stronger receiver selective-opening and chosen-ciphertext settings:
  https://eprint.iacr.org/2016/1083 and https://eprint.iacr.org/2018/755
- Lattice OW-ChCCA/tight bilateral selective opening, stronger/different
  tools and security definition: https://eprint.iacr.org/2023/823
- NIST standardized KEM baseline: https://csrc.nist.gov/pubs/fips/203/final
- Threshold interface and adaptivity context, not equivalence:
  https://csrc.nist.gov/pubs/ir/8214/c/final

## Barrier for explicit single-support coupling catalogs, even without replication

Fix an intact family by disclosing all other family keys, a simpler subgame.
Work at the level of abstract deterministic coordinate shares produced from
dealer coins, with exact correctness from surviving endpoints after any f
outages, across both challenge messages. For a coupling that changes the
message while leaving the plaintext coordinates outside a fixed endpoint
support W unchanged, necessarily |W|≥f+1: if |W|≤f, erase W, and the exact same
surviving shares would decode to both messages. This hypothesis concerns
share-only reconstruction in this intact-family slice with the other
families' same coordinates; the argument also applies with fixed identical
public auxiliary data passed to the decoder. It does not apply to a
decoder receiving separate setup-dependent correlated secrets or controls
that the coupling changes outside W.

In this model an explicit proof catalog of fixed supports, where every
allowable corruption C must admit a candidate support W disjoint from C,
has the same counting obstruction. Each W covers no more than binom(n−k,c)
c-sets (k=f+1). At n=c+k, every C forces W=[n]∖C, so at least binom(n,c)
distinct supports are needed even for a different exact-correctness share
code, including Shamir. This excludes polynomially enumerating individual
support-conditioned couplings near the cut for dense c,f. It does **not**
prove a black-box separation: a proof might treat the support symbolically,
use a different hybrid, emplace a noncommitting primitive, or avoid this
description of a witness entirely.

## Verification

Lean checks supporting arithmetic for the architecture, not the adaptive security reduction. The controls are synthetic, not actual KEM invocations. With compiled Mathlib at commit d13f23b723b8a846827a245b89c10fc7d3f11612, run LEAN_BIN=/path/to/lean MATHLIB_DIR=/path/to/mathlib4 bash replay.sh.
