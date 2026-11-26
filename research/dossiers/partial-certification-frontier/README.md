# Exact partial-certification frontier for Byzantine recovery

## Model
A scalar block value x from an alphabet of at least two elements is placed
identically in k labeled endpoint domains. A fixed h of those k domains are
certified: if their reports are accepted by a trusted certification rule,
the value is x, and a live honest certified domain always returns an accepted
correct report. For all other domains the receiver only knows the domain
label, not whether the report is truthful. One report per domain, fixed valid
roster for this challenge, independent of x in the ideal model. There are up to
f fault domains with no report, and up to b *other* Byzantine domains which may
choose arbitrary reports or withhold. In the ideal model unavailable/rejected
certified copies carry no auxiliary information about x. The receiver has no
side input encoding x. The two budgets are total endpoint-domain budgets,
not per-block budgets; for a single fixed block their intersection with its
honest/certified/opaque supports can be arbitrary.

**Theorem.** Zero-error reconstruction in this model is possible if and only if
both
  (1) k ≥ f+b+1
  (2) k+max(0,h−f) ≥ f+2b+1.
Consequently in the shortest feasible block k=f+b+1 and b>0, all but one copy must
be certified. For k between f+b+1 and f+2b inclusive and b>0, the number of
certified copies is exactly h_min=2f+2b+1−k; for k≥f+2b+1 it is zero. When b=0,
no certification is needed at any recoverable k. This states minimal h within
a fixed per-copy certification interface, not minimum cryptographic metadata
bits across all protocols.

## Proof
If an accepted certified report is present, use it. If h>f+b, at least one
exists. Otherwise the worst case without one spends min(f,h) outages and
max(0,h−f) Byzantine domains covering the certified positions. This worst
allocation claims a maximum on weighted opaque faults, not a bound on each
kind separately: if e certified slots are unavailable through outages, then
at least h−e Byzantine slots are used on certified positions. The maximum
possible opaque load (one per outage and two per Byzantine position) is
  f−e+2(b−h+e)=f+2b−2h+e,
maximized at e=min(f,h), feasible when h≤f+b. A strict majority of surviving
opaque reports equals x whenever u=k−h exceeds that load: counting Byzantine
withholding as a potential erroneous report only strengthens the guarantee.
Rearrange to (2). When h>f+b and k≥h, both inequalities automatically hold.

For (1), when k≤f+b withhold all reports in two different-value worlds.
For (2), assume (1) and h≤f+b. The case h>f+b cannot violate (2), since k≥h. Erase all e=min(f,h) certified positions by true outage in both worlds, and have the same h−e Byzantine certified positions abstain (or return the same fixed syntactically invalid report) in both worlds. No value-dependent certificate or failed-proof data is passed to the ideal decoder. Use f'=f−e remaining outages on the opaque
positions, leaving N=u−f'>0 by (1), and b'=b−(h−e) remaining Byzantine domains.
If (2) fails then N≤2b'. Split the same N visible opaque positions into
two sets of at most b'. Return x₀ on one set and x₁≠x₀ on the other, assigning
Byzantine slots to the wrong-valued set in each world. The budgets are upper bounds; no padding is needed. If exactly b domains must be listed and the universe permits it, mark extra live domains Byzantine but let them give their same honest reports; this does not change either view. The full reports
are identical in these two worlds. Even a randomized decoder cannot have
worst-case failure below 1/2 on this indistinguishable pair.

## Corollary for independently reconstructed adaptive envelope blocks
Use the passive adaptive envelope's additive block sharing and witness sets,
with block supports chosen to meet the theorem. With fixed c disclosures
the witness condition is unchanged, since the compromise of *any* copy
reveals the block value, certified or not. For disjoint supports at each
width k, c+1 blocks are necessary and sufficient; this uses (c+1)k domains
per family, reusable across families. If fewer endpoints are available, use
an explicit covering family as in the passive envelope, with the same
covering-number obstruction at the smallest n=c+k. This claim is targeted
to independent per-block reconstruction; arbitrary cross-block code or
multiple-block joint verification is not covered.

Example f=2,b=3: short block k=6 requires h=5, intermediate k=7,8 require
h=4,3, and k=9 is fully opaque. For b>0 the achievable nonzero branch
trades one certificate-bearing copy per extra total copy, then the last
extra copy permits dropping f+1 remaining certificates. At k=f+2b the
required h is f+1 (so the drop to zero is f+1). This is a communication
accounting claim, not a latency comparison. With a simple linear cost A k+S h, A,S≥0 and
b>0, the optimum over all configurations is attained either by the shortest
(f+b+1,f+b) or all-opaque (f+2b+1,0) choice: the nonzero branch has constant
slope A−S, and if the slope is negative the final drop costs no more than the
previous point. Short wins iff b A≥(f+b) S (ties allowed). An intermediate
point can still matter under a hard cap on total domains or certified domains.

The hidden-signature realization uses one signature-generation operation per
block with h>0 but h transmitted fixed-length signature fields. Ordinary
fully authenticated repetition at the short length would transmit one more
such field; the exact frontier certifies all but one. A publicly signed
Merkle root can amortize one signature across blocks, but a public root over
raw values is not automatically hiding and a root over ciphertext alone
does not verify a plaintext report. An alternative design could use
independently statistically hiding binding commitments as leaves, a
collision-resistant quantum-secure Merkle tree and one trusted signed
root; include openings and authentication paths inside the certified
payloads. This may reduce signature work while adding commitments/opening
traffic; no bit-optimal claim for our per-copy interface.

## Realization under scoped PQ assumptions
Choose an authenticated independent dealer verification key fixed before
setup. Under a post-quantum EUF-CMA signature scheme, the honest dealer
signs a canonical injective encoding of (unique envelope ID, roster/policy
ID, family/block label, block value), once per block with h>0. Include that
signature **inside** the encrypted payload at its h certified domains,
not in the public metadata; repeated copies can use the same signature,
and certification must be authorized by a fixed authenticated copy roster.
Payload formats and mask lengths are public and independent of the block
value (fixed length or canonical padding). The receiver validates under
the dealer key; an invalid certified report is an erasure and is never
counted as opaque. A false accepted value yields a new-message signature
forgery, since the dealer substituted no alternate signature for the same
envelope/policy/block tuple. Replay of a genuine block value is not a
correctness problem; unique context excludes replays of different blocks
and challenges. Treat collective compromise, replacement of the receiver's
trusted configuration, or sender signing-key loss as out of scope.

Integrity reduction: simulate setup, other KEM credentials, share values and
online requests in the honest-dealer experiment while using an ordinary
classical signing oracle for the h>0 blocks, and output the first accepted
wrong-value certified tuple/signature. Acceptance of valid but wrong
values has probability at most the signature forgery bound in the entire
simulation (no extra guess of a block needed). Conditional on no such event,
the ordinary ideal per-block decoder proof applies, subject to honestly
generated capsules decapsulating correctly. Standard KEM key agreement
failure is an additional explicit union-bound error and is not silently
absorbed into the f, b budgets. Opaque reports and reports with invalid
metadata are bound to their pre-assigned endpoint labels by the specified
receiver interface; adversarial creation of arbitrary new endpoint labels
is not modeled. Shared transport failure outside f is also not modeled.

Passive disclosure confidentiality retains the canonical intact witness
proof (where the receiver gives no reconstruction transcript or validity
oracle). Extend the masks for certified payloads with a PQ PRG. In each
chosen witness block replace the entire mask on each copy by independent
uniform, using no witness receiver private key before early abort. Changing
the challenge secret shifts one block value; use the same distribution of
fresh dealer signing coins on both sides, sign the changed value, and shift
each chosen uniform mask by the XOR difference of the entire fixed-length
plaintext, including signature. This preserves all public ciphertexts and
all legally disclosed values pointwise. No verification status observable
from a challenged receiver may be added without a separate composition
proof. This is honest-dealer recovery integrity and separately oracle-free
adaptive disclosure privacy, **not** active selective-opening/CCA security,
a deployable service protocol, verifiable secret sharing against a
malicious dealer, or an original KEM.

## Primary prior context
- Cevallos, Fehr, Ostrovsky, Rabani, *Unconditionally-secure robust secret
  sharing with compact shares*, EUROCRYPT 2012, and Fehr/Yuan,
  *Robust secret sharing with almost optimal share size and security
  against rushing adversaries*: see author bibliography
  https://homepages.cwi.nl/~fehr/publications.html . Their robust secret
  sharing addresses more general share corruption, often without a
  protected dealer signing key and with stronger recovery-transcript
  security; no claim of beating those protocols or novelty for auth.
- NIST FIPS 204, ML-DSA signature interface and fixed sizes:
  https://csrc.nist.gov/pubs/fips/204/final .
- NIST IR 8214C threshold protocol scope:
  https://csrc.nist.gov/pubs/ir/8214/c/final .
- *Byzantine Consensus in the Partially Authenticated Setting* (primary entry:
  https://iris.landsbokasafn.is/is/publications/byzantine-consensus-in-the-partially-authenticated-setting/ )
  and *Byzantine Agreement with Authentication: Observations and
  Applications in Tolerating Hybrid and Link Faults* (primary author page:
  https://www.csl.sri.com/papers/dcca95/ ) address agreement with distributed
  processes and partially available authentication or mixed faults, not
  this one-shot identical-block receiver with a protected honest dealer.
  No resilience comparison to consensus.
- Classical error/erasure criterion for repetition (2b+f<k) is the opaque
  endpoint of this result; the distinction is a hybrid coordinate class
  where Byzantine modifications in certified positions count only as loss,
  and the exact integer budget tradeoff for this class. Priority unclaimed.

## General q-ary codes: exact optimal frontier and efficient Reed–Solomon decoder

Consider any injective q-ary code of q^K messages, 1≤K≤n, with a fixed
set H of h certified coordinate positions and the same (f,b) budgets.
Certification now authenticates the *correct value at that coordinate*.
Receiver input contains accepted coordinate values or erasures and no
auxiliary data. For each pair of distinct codewords, let D be their
difference support. The possible report sets intersect iff the repeated
block ambiguity criterion fails with k=|D| and h_D=|H∩D|. Indeed on D the
two competing correct values differ coordinate by coordinate, so the
same split argument works using the respective pair's symbols at each
site. Outside D everything can report the common correct symbol. For
the converse, restrict any purported shared report to D, obtaining
an intersection inside the same budgets. Recovery is equivalent to
satisfying both inequalities for every D.

Define d=n−K+1 and H*=max(0,h−(K−1)). The universal exact frontier is
  d ≥ f+b+1  and  d+max(0,H*−f) ≥ f+2b+1.
Necessity for *any* q^K-message code: choose K−1 coordinates containing
as many certified positions as possible. Only q^(K−1) projections
exist, so some two codewords agree on this entire chosen subset. Their
difference support satisfies |D|≤d and h_D≤H* simultaneously. Since both
repetition inequalities are monotone in the two support counts, they
force the displayed frontier. Sufficiency whenever a distance-d MDS
code exists: all difference supports have size ≥d and omit at most
K−1 certificate positions, hence h_D≥H*. A Reed–Solomon evaluation code
gives this when q is a prime power with q≥n. This is a joint redundancy
and prescribed-verification-count theorem, not a new code or encryption
primitive.

Explicitly, the least n is K+f+b when unrestricted certification is
available. If b>0 and K+f+b≤n≤K+f+2b−1, the least h is
2K+2f+2b−1−n. At n≥K+f+2b no certification is needed. At the shortest
n, h=n−1 suffices (and is necessary when b>0). If b=0, at n≥K+f no
certification is needed. For example, with K=32, f=3 and b=4, the
frontier allows n=39 with h=38, n=42 with h=35, or n=43 with h=0.

Efficient decoder (Reed–Solomon): let ℓ be accepted certified locations,
and let z be the total number of missing/rejected locations. If ℓ≥K,
interpolate outright. Otherwise let B'=b−max(0,z−f). It upper-bounds remaining errors because
every excess erasure beyond the outage budget consumes a Byzantine
domain distinct from an opaque value error. Reject if B'<0, an impossible
view. Here z≥h−ℓ≥H*. The frontier implies n−K≥z+2B': for z≤f, use H*≤f
and n−K≥f+2b; for z>f, use
z+2B'=2f+2b−z≤2f+2b−max(f,H*)≤n−K.
Discard the z erasures and apply ordinary unique RS decoding with up
to B' errors to the remaining evaluations, e.g. via Berlekamp–Welch.
The certified evaluations are exact and may also be used for verification.
This section is an ideal report-level integrity result; arbitrary
coding can change which coordinate coalitions learn the payload.
The previous adaptive confidentiality proof does not apply to the
MDS variant merely by substituting the code.

Coding references: the Singleton projection and Berlekamp–Welch tools are
standard (see the original Welch–Berlekamp patent,
https://patentimages.storage.googleapis.com/18/a2/dc/e8b3cbff1865cb/US4633470.pdf). Masnick and Wolf's foundational unequal
error protection paper (https://doi.org/10.1109/TIT.1967.1054047) distinguishes
which *message symbols* require stronger recovery; our channel instead
prescribes strengthened *coordinate reports* and requires recovery of the
entire message. No claim of priority for weighted channel-ball arguments.

## Verification boundary

Two Lean 4.34.1 files independently verify arithmetic supporting the bounds
and the decoding budget. They do not formalize the information-theoretic
channel model, Reed–Solomon correctness or the signature reductions.
The synthetic enumeration is a model check, not deployment or benchmarking.
