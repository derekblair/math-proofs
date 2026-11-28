# Native-wire PQ custody: packed seed responses versus volatile snapshot resistance

## Three different models

1. **Native KEM in a trusted volatile combiner.** A trusted dealer
   generates a native KEM seed, provisions opaque, perfectly private
   shares, and never exposes its seed. The combiner reconstructs the
   seed inside trusted volatile state only for an authorized call,
   computes the exact native decapsulation, then erases it and its
   expansion. Any disclosure of its active reusable secret buffer,
   leakage through authorization endpoints, hostile response
   substitution or bad erasure is excluded. Availability assumes
   honest responders, not Byzantine delivery. The adversary can
   select up to c classical custodian-share disclosures per epoch
   adaptively and makes aggregate-only classical CCA calls while
   retaining arbitrary QPT computation.
2. **Independent-slot signed envelope with a limited volatile view.**
   Each endpoint privately performs its independent KEM decapsulation
   and exports only a full-context-derived PRF pad, never its reusable
   private key or its raw KEM output. A combiner learns selected pads
   and underlying shares for that ordinary context, plus the decoded
   result. An additional snapshot oracle may reveal these values for
   arbitrary *nonchallenge* accepted contexts, not a session that is
   currently processing, has cached, or later processes the challenge.
   No endpoint private buffers, authorization credentials or hostile
   replacement of receiver selection are given by this snapshot.
3. **Native-format genuine threshold evaluation.** An interactive
   MPC may instead compute native decapsulation without ever
   reconstructing the reusable key. Its output, internal corruption
   and availability claims must be audited under its own game.
   Neither the trusted-seed separation nor the ideal response
   cut below rules out that possibility.

A full combiner snapshot during the challenge can reveal its plaintext/
test key in every model that lets that combiner recover it; this is
excluded throughout. No implementation/certification/deployment claim.

## Packed fixed contact count for the trusted native profile

FIPS 203 KeyGen uses independent 32-byte seeds d and z. NIST's PQC FAQ
(revised June 2026) accepts the 64-byte pair as a private-key format
for later expansion. HQC's October 2026 author specification Table 9
reports a 32-byte secret decapsulation seed for HQC-3; this is not an
approved finalized FIPS specification. Treat each uniformly generated
seed as an H-bit string (ML-KEM H=512). Fix t>c responders out of n
and f outages with t≤n−f. Choose
  L=t−c,
  w=max(ceil(H/L),ceil(log₂(n+1))).
Take F_(2^w), n distinct nonzero evaluation sites, and split the
padded seed into L field symbols. Place these in coefficients of
degrees c..t−1 of a random degree≤t−1 polynomial; independently
uniform low c coefficients in degrees 0..c−1 mask them. Each
custodian stores one w-bit field element. Deterministically select
t available responders, each returning its share over a confidential
authenticated channel into the trusted state. Interpolate, extract
the seed, and run ordinary expansion/decapsulation locally. Only
the one base ciphertext is public, and seed bytes need not be sent
as part of responder queries. The two arithmetic proof pieces are:
- Any t distinct responses interpolate the full polynomial exactly,
  so any f permitted outages leave at least t.
- For any e≤c distinct revealed sites, the evaluations of the
  initial e low monomials already have invertible Vandermonde
  matrix. Thus the entire e-share view is uniformly random over
  F_(2^w)^e conditional on every fixed seed. Extra low coefficients
  only add independent noise.

The same adaptive share simulation requires no final-exposure guess.
For each track and epoch, return an independent uniform field symbol
on first disclosure of any permitted distinct label, with a cache on
repeats; each next symbol conditioned on earlier ones is uniform
even conditional on the real secret and public key. Base aggregate
decapsulation outputs are conceptually base CCA-oracle answers and
depend on the seed, not the custodian masks. Therefore their
observations do not invalidate the induction for mixed adaptive
CCA and share disclosures. For independently remasked epochs, the
argument repeats using fresh caches per epoch; assume trusted atomic
redistribution, hidden transport and old shares securely absent in
the corruption window, not mobile-coalition leakage over overlapping
stored versions. This is a proof of the abstract profile only.
The aggregate CCA interface rejects the exact challenge base ciphertext,
including an equivalent external wrapper encoding. No observable metadata
may depend on the random low sharing coefficients.
No threshold-decapsulation transcript is visible. For a single
family no extra target-authorization guess appears; if an entire
family's seed may be exposed, a hybrid can branch by the first
good intact family with early abort, plus whatever base combiner
assumptions are needed. Unlike the independent envelope, there is
no guessed endpoint subset in this trusted-seed proof.

## Exact static response cut and contact/byte break-even

Let S be the seed, A any fixed decoder-available public advice,
and Y_i the selected responder words, of fixed length b_i bits
(or bounded lengths padded with unambiguous encoding). For a
fixed selected t-set T assume:
- exact recovery from A and Y_T, with no other seed-dependent
  input at the combiner;
- for every J⊂T of size c, I(S;Y_J | A)=0.
Then for every such J,
  H(S|A)=I(S;Y_(T\J) | A,Y_J)≤Σ_(i∈T\J)b_i.
Thus the sum of its shortest L=t−c widths is ≥H(S|A), and the
total width is ≥ t H(S|A)/(t−c). For integer widths and integral
B=H(S|A), one also gets total ≥B+c·ceil(B/L): the largest of
the L shortest is at least ceil(B/L), as are all c remaining.
These are worst-case fixed-width bounds, not bounds on arbitrary
interactive MPC or variable-length inputs without a framing model.

For the **no-advice reconstruction class**, exact recovery holds
from shares alone and privacy is unconditional before the KEM
public key is specified; one may apply the cut with A empty and
H(S)=512. A genuine KEM public key is statistically tied to its
secret; for any reconstruction scheme allowed to exploit it as
advice one must use H(S|public key), not assume it is 512.
Application of classical communication-efficient secret sharing
to seed custody is the architectural point here; the entropy cut
and ramp packing are prior (Huang–Langberg–Kliewer–Bruck,
https://arxiv.org/abs/1505.07515). Universal contact-count schemes
also already exist (Bitar–El Rouayheb,
https://arxiv.org/abs/1512.02990); our packed example fixes t
and does not claim their adaptive-bandwidth optimality simultaneously.

Illustration: at c=63,n=130,f=6, choose t=85 to match the prior
nested wrapper's worst selected endpoint count. For a 512-bit
seed, L=22,w=24. Static payload responses use 255 bytes, close
to the no-advice integer lower (512+63·24)/8=253 bytes.
The threshold contact choice t=64 instead costs 4,096 response
bytes for ML-KEM; it can be held by n≥70. Increasing contacts
therefore strongly decreases responses in this model, without
adding local KEM invocations. For HQC H=256, t=85 gives w=12
and 127.5 bytes bit-packed, or 170 bytes when individual
replies use whole-byte words.

Keep the following directions distinct:
- **Unauthenticated/public sender-to-receiver core:** one ML-KEM-768
  base ciphertext is 1,088 bytes (FIPS 203 Table 3); the comparable
  independent KEM-wrapper's 130 slots cost 130·(1,088+32)=145,600
  bytes, before wrapper signature, nonce and framing. A simple
  ML-KEM-768 + HQC-3 native hybrid core has two capsules totaling
  10,066 bytes before any protocol framing/combiner context;
  the independent two-family wrapper core is 1,316,900 bytes.
  Compare session-key encapsulation to session-key encapsulation,
  not 32-byte PKE to a raw KEM. HQC-3 8,978-byte constant is
  the author specification, not final FIPS HQC.
- **Custodian-to-combiner responses only:** one native ML-KEM
  ramp with 85 selected custodians sends 255 payload bytes;
  two families send 382.5 bit-packed or 425 with byte-aligned
  individual words. The independent wrapper with 85 selected
  endpoints sends 2,720 bytes of pads/family, or 5,440 across two.
- **Combiner-to-custodian requests:** excluded from those response
  counts. Native seed share collection does not need to send the
  base ciphertext beyond the trusted combiner, but authentication
  and policy messages cost real bytes and may require binding.
  The independent envelope must send at least each selected
  component ciphertext to its local processor unless cached,
  plus a securely recognized whole-context representation. A
  protected context authenticator and collision-resistant digest
  might reduce repeated sending, but those are not silently
  assumed to be free. End-to-end communication/latency is not
  inferred from a response-only arithmetic comparison.

## Reusable-key separation under nonchallenge snapshot

Fix a long-lived epoch public key and compare two experiments on a
challenge, with the restriction that its exact plaintext/key is never
an allowed output. In a raw native evaluator that reconstructs the
same reusable seed, one full volatile snapshot at *another* valid
decapsulation includes that seed or an equivalent decap secret.
By ordinary native correctness, this value is sufficient to determine
the key of any valid ciphertext under that public key. Thus exposing
that exact state is incompatible with the intended model. This is a
logical implication in the ideal snapshot model, not an exploit
claim about a machine or an impossibility for true threshold MPC.
Erasing a previously disclosed seed or refreshing its at-rest
shares does not restore privacy for that same reusable public key.

Conversely the independent wrapper can grant the above ordinary
nonchallenge pad snapshot extension under the already established
per-slot KEM/PRF model. Verify and enforce the exact signed context
guard; context includes epoch, canonical complete indexed base
ciphertext list, fresh nonce, verification key, and any approved
incidence label. Any identifier digest design would need its
own collision/binding assumption. Endpoint API must return only
the scoped pad, never a raw shared key and never an authorized
operation for a pending/exact challenge context. If the challenge
base capsule appears at another context, the fixed-slot simulation
uses the same candidate base secret to derive the distinct PRF
output in every allowed context. Only those derived values—not
candidate keys—are revealed in the extra oracle or snapshot.
The witness's exact challenge-context PRF input is guarded;
after the protected-key PRF hybrid that mask is independent
of all snapshots at other contexts. Extending the usual coupling
of challenge masks to the recorded pads, intermediate recovered
share values and deterministic combiner output preserves the
entire allowed transcript. No additional guess is introduced by
snapshot *queries* (the original reuse/domain cap and QPT PRF
bounds account for all the needed calls). This proves only the
specified view extension, not arbitrary process memory leakage
or an active aggregate takeover. Long-term secrets for authenticated
local channels must stay outside the snapshot or be separately modeled.

## Stronger native MPC baseline, not a rebuttal

Ta–Liu–Chau–Wang ePrint 2026/2220 Scheme A keeps exact virtual
ML-KEM format/outputs and does not reconstruct its private key.
Its proof is static semi-honest MPC with trusted preprocessing,
not adaptive, malicious or guaranteed delivery. The abstract
reports 218 rounds for ML-KEM-768; its Table 1 and Appendix C.1
count 217 in the online decapsulation circuit, with final key output
reconstruction conceptually separate. Its Table 3
at (threshold,N)=(2,3) lists 360 kB outgoing per party and a
72 ms same-machine simulation median for category 3. These are
published internal protocol metrics at a completely different
parameter point, not a real-network or n=130 timing comparison.
The noncompatible 35-round Scheme B is not native ML-KEM.
See https://opencryptology.org/2026/2220.pdf .

Latest retrieved Giorgi–Laguillaumie–Ottow–Vergnaud 2026/946
provides HQC threshold PKE decoding, with 87 rounds and estimated
7.21·10^7 secure multiplications for its category-3 decoding
profile (Table 4), explicitly leaving full threshold IND-CCA
construction future scope in its discussion after Table 6. Do not equate its
HQC.PKE lengths and decoder costs with a full hybrid native
HQC KEM. See https://opencryptology.org/2026/946/versions/20261120T190610Z.pdf .
Amber is another important point, a native lattice threshold KEM not
compatible with ML-KEM ciphertexts. Its NIST preview §2.2 separates
the Shamir variant's adaptive CCA with no extraction-share robustness,
from the Vandermonde variant's stronger robustness with static corruption.
It assumes trusted setup, synchrony and broadcast. Its presentation
quotes three rounds plus combine and 28,544-byte ciphertexts for the
Shamir variant at the specific threshold 32 of 64; this is not pricing
a 64-of-130 category-3 instance nor vouched QROM proof here.
https://csrc.nist.gov/csrc/media/Projects/threshold-cryptography/documents/TCall-1/Amber-PW01.pdf
and https://csrc.nist.gov/csrc/media/presentations/2026/mpts2026-3b5/images-media/mpts2026-3b5-slides-amber-lapiha.pdf .
The [NIST Adamas preview](https://csrc.nist.gov/Presentations/2026/tcpt3-4a2)
likewise reports one-round schemes and CCA security under adaptive
corruptions in its own model. It is not measured in this dossier, and the
raw-seed-model separation does not rule it out.

A properly proved threshold MPC with a suitable compromise view
could in principle bring native wire plus nonchallenge snapshot
tolerance; neither of our simple profiles rules it out.
No new KEM or claim of improved hardness/real-time security.

NIST primary seed FAQ https://csrc.nist.gov/Projects/post-quantum-cryptography/faqs ,
FIPS 203 https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.203.pdf ,
HQC October author specification https://pqc-hqc.org/doc/hqc_specifications_2026_10_12.pdf ,
and scope of NIST threshold work https://csrc.nist.gov/pubs/ir/8214/c/final .

[StaticWidth.lean](StaticWidth.lean) checks the conditional integer-width
inequality and the 253/255-byte arithmetic in Lean 4.34.1 / Mathlib v4.34.1.
Run `python checks.py` for finite ramp and width checks. The entropy and
security arguments are reviewed paper proofs, not Lean. See [review](REVIEW.md).
