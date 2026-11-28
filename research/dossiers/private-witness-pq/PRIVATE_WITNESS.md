# Private randomized witnesses for the active envelope

## Result

The public covering catalogue is unnecessary for the one-block active
envelope *reduction*. At wire cost n independent copies per family,
degree n−f−1 Shamir and c cumulative endpoint disclosures, its
polynomial-factor loss can use
  1/p = binom(n,r)/binom(n−c,r),  r=f+1,
where n≥c+f+1. There is no catalogue generation or correctness event.
A support is a private coin of the reduction, not a publicly sent
metadata item or a decoder rule. This reaches the already-known
minimax reciprocal-success cost for a prior, independent fixed support
(WITNESS-MINIMAX.md) with an explicit executable-in-polynomial-time
hybrid argument, rather than enumerating all binom(n,r) supports.
It is not a tight bound for all proof techniques or a new base KEM.

## Game and precise reduction

Retain the active wrapper assumptions: authenticated fixed roster and
indexed KEM key slots; independent honest KEM key/encapsulation coins;
PQ IND-CCA with classical KEM queries for at least one undisclosed good
family; independent PQ PRF and strong one-time signature; a trusted
aggregate-only classical CCA oracle available to an internally QPT
adversary; no same-key legacy non-aggregate service; deterministic
available-site selection and generic failure behavior, no side-channel
or compromised aggregate output. Raw endpoint/family key disclosures
are adaptive and may occur before or after challenge. Every transcript
must leave a good family intact and expose at most c endpoint domains.

Each family has one degree (n−f−1) sharing of its additive offset,
at n distinct nonzero sites in a sufficiently large field. Sender uses
one independent KEM capsule and full-context PRF mask at each slot,
with the same signed whole-body guard. Exactly n−f available members
recover each family offset. No construction step refers to a protected
support S. Use the prior correctness consistency convention globally:
pre-sample honest challenge KEM capsules independently of the chosen
message, and in the proof adopt the encapsulated key for same-index
exact challenge-component reuse, while charging honest correctness
failure over all challenge slots. This global convention is symmetric
in S. The prior exact-context guard changes overall advantage once
by its strong one-time signature and prechallenge nonce-guess terms.

Fix a good family i. Let P_b(i) be probability in that guarded,
consistency-convention real experiment that the adversary accepts and
i is the first good undisclosed family in its final record. The
definition uses a fixed total family order. Pad its final actual
exposed domain set to a c-set D by a public deterministic rule, e.g.
first unused sites; this padding is not disclosure. Independently of
this experiment choose uniformly an r-set S of the roster. Consider
the restricted event that the same acceptance and classification
hold and S misses D. Because the real experiment never uses S,
conditional on every transcript the probability of the latter is
exactly p, regardless of adaptive query history. Consequently
  P_b^S(i), averaged over private S = p·P_b(i).
This is an equality of unnormalized probabilities, not conditioning
of the adversary or any oracle on survival.

A reduction samples private S before giving out the roster. It chooses
an indexed member of S for its current single-KEM or PRF hybrid and
places that challenge key there, generating all other honest slots
independently. This programming does not change the distribution of
the real-world roster or transcript because all slots in the designated
family have the same independent key distribution. The sampled order
of S may be fixed lexicographically after drawing it; there are only
r positions to telescope, not one reduction per actual S. Stop with
output zero on any actual disclosure touching S or all of family i:
it cannot contribute to the restricted event. Determine first-good
classification and the extra padded-set exclusion only at completion.
Thus the simulation never discloses a slot private key it does not
know. Decapsulation handling remains per indexed slot: substitute the
given real/random candidate on exact challenge-component reuse and
forward only other component ciphertexts, with the prior exact-context
guard, deterministic receiver selection and failure handling unchanged.
There is no guess of the order or time of endpoint exposures.

For fixed S, once its masks at the guarded challenge context are
independent uniform outputs, choose the normalized vanishing polynomial
  H_S(X)=∏_(a∈[n]\S)(1−X/a).
Its degree is n−r=n−f−1, its constant is 1, and its values vanish
exactly on the other sites. Shift the chosen family polynomial by
the challenge message difference times H_S, and adjust only the S
masks at the challenge context. This is a bijection of uniform share
arrays. It gives the same signed ciphertext, all other plaintext/share
values held fixed, and the same classical response interfaces on every
non-aborted branch, so the acceptance, final classification and
padded-set test agree in both ideal worlds. Uniform PRF outputs at off-challenge contexts stay
independent. More explicitly, denote the restricted acceptance
probability at intermediate hybrid t by A_(b,t)(i). Let t=0 be the
unchanged real-source experiment, t=r the fully random candidate
keys, and t=2r the fully replaced protected PRF instances. Then
\[
 A_{b,0}(i)=pP_b(i),\quad A_{0,2r}(i)=A_{1,2r}(i),\quad
 |A_{b,0}(i)-A_{b,2r}(i)|\le r(\epsilon_{\rm KEM}+\epsilon_{\rm PRF}).
\]
Thus p|P_0(i)−P_1(i)|≤2r(ε_KEM+ε_PRF). This passage does not
announce S or divide by a hybrid-dependent probability. The final
classification uses only the adversary's classical disclosure labels
and the fixed good-family designation used by the reduction;
padding and the disjointness check read no challenged secret keys.
Sum over candidate families. With R families and worst-case
per-slot `ε_KEM, ε_PRF`, a sufficient active privacy bound is
  ε_guard + ε_global_correctness
    + 2Rr(ε_KEM+ε_PRF)/p.
Here the guard and global correctness terms mean total advantage loss across both
challenge worlds, not a per-world failure probability. The early termination, padding and private S are proof operations
only. The actual encryption scheme and ciphertext format do not
change from the one-block envelope; even a previously public catalogue
need not be generated, stored or consulted for this new proof. A public S announced to the adversary would invalidate the
independence equality. All correctness and guard terms here are
applied before the support experiment, so the 1/p factor need not
inflate them.

If a non-uniform private witness law is used with efficiently
computable avoidance π(D)≥π_min>0, a final extra acceptance coin of
probability π_min/π(D) restores the same normalization on unmodified
real worlds. This is a general optional artificial-abort variant,
not a proof that every topology has an efficient such law.

## Wire and proof-cost comparison

At n=(1+δ)(c+1)+O(1), fixed δ>0 and f=a ln(c+1)+O(1), the support
loss is 1/p=(c+1)^(a ln(1+1/δ)+o(1)), with no extra linear factor from
a public, universally covering list. If n=c+f+1, p=1/binom(n,r), so a
genuinely polynomial loss in joint large parameters is not automatic.
This is a proof reduction count, not computational or hardware speed.

At c=63,f=6,n=130, p≈0.0082323750, 1/p≈121.4716284. Earlier checked
public portfolio used W=4,678 at the same 130-slot wire, but receiver
selected 88 instead of 124 decaps/family. The old tight layout W=7,788
selected 64. Those are meaningful decoder/proof-factor alternatives.
One family needs 130·(1088+32)=145,600 core bytes using independent
ML-KEM-768 versus 448·(1088+32)=501,760 for independent replicas;
the documented category-3 batched mKyber replica control is 240,064.
The two-family ML-KEM-768/HQC-3 example needs 1,316,900 core bytes;
the batched lattice/independent HQC replica control needs 4,276,544.
All counts omit same nonce, signer and framing. A single-endpoint
ML-KEM-768 ciphertext is still only 1,088 bytes, and a conventional
hybrid is much smaller, but neither supplies this distributed raw
endpoint-disclosure property. HQC-3 size 8,978 is from the Oct 2026
author specification, not final FIPS. A compatible threshold ML-KEM
may keep the 1,088-byte public wire but changes the trust/interactive
decap model and has other overhead; this dossier does not surpass it
on wire or claim throughput. Post-quantum hardness and endpoint
adaptivity remain distinct assumptions.

Sources: FIPS 203 https://csrc.nist.gov/pubs/fips/203/final ;
NIST transition/approval status https://csrc.nist.gov/pubs/ir/8547/final ;
HQC author spec https://pqc-hqc.org/doc/hqc_specifications_2026_10_12.pdf ;
mKyber CCA table https://cryptojedi.org/papers/mkem-20220812.pdf ;
compatible threshold work https://eprint.iacr.org/2026/2220 and
https://csrc.nist.gov/pubs/ir/8214/c/final . No priority, underlying
primitive novelty, interop, validated security or deployment claim.
