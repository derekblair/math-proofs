# One-block envelope game used by the proof

This is a research model for a bounded raw-key-disclosure problem. No
proposal to deploy it, replace a standardized KEM, or expose a local
decapsulation service is made here.

## Fixed inputs and interfaces

The setting fixes an authenticated roster, independent key pairs per
indexed endpoint and family, and an injective canonical encoding of every
ordered index and vector. At least one good family, fixed in the security
analysis, stays entirely undisclosed. The adversary can adaptively expose
up to c endpoint domains and entire other families. The transcript records
these disclosure labels. At most f sites may be unavailable; the trusted
aggregate decoder chooses n−f available members of each one-block family
by a fixed rule, independent of values and failures. It returns only the
aggregate plaintext or the same generic failure. No other same-key oracle,
side-channel, dishonest receiver output or Byzantine site response is
modeled. A quantum-computational adversary has classical interfaces only.

## Challenge context, masks, and guard

Each family selects one field-element additive offset with the
sum of all offsets equal to the message (the field may be any sufficiently
large finite field). Its Shamir polynomial is uniformly sampled at degree
at most n−f−1 with that constant. Independently encapsulate each base KEM
slot. The challenge mask input includes a fixed protocol/roster tag, the
fresh uniform nonce, the one-time verification key, the complete ordered
indexed vector of capsule bytes, and the mask slot. It does not include
the masks themselves, so there is no circularity. Sign the canonical body
including the complete context and masked shares. The trusted decoder
verifies the signature before processing; this does not authenticate a
sender not otherwise authenticated by the application. It interpolates
the family constants and adds them. Exact challenge ciphertext queries
are excluded in the usual chosen-ciphertext game.

A guard experiment excludes any query reaching the challenge PRF input
under an exact challenge context. After the challenge is issued, a
different accepted body or signature at that context would give a
strong one-time forgery, while an exact repeat is already excluded.
Before the challenge, the independent uniform challenge nonce limits
accidental reach to at most the number of classical queries times the
per-query guessing bound. This reasoning requires injective indexed
encoding and no other PRF access outside the model. Separate success
probability differences in both message worlds are included in the
total guard loss.

A consistency experiment substitutes the encapsulated key for reuse
of the exact challenge component at its original key index in any
other accepted context. It differs from ordinary deterministic base
decapsulation only on honest challenge correctness failure. Apply
the union bound across the challenge slots and both message worlds
before choosing the private proof support. A base KEM reduction
placed at one indexed slot may forward different component ciphertexts
to its permitted decapsulation oracle. It does not forward the
challenge component at that index, and can compute all other slots
it generated. A PRF reduction at that slot substitutes the chosen
function for its randomized challenge key instance and uses independent
outputs at distinct encoded inputs. Revealing the challenged raw
key is never simulated on trajectories that could contribute to
the restricted acceptance event. Each hybrid must run in the common
classical-query/QPT interface defined above.

The [private-witness proof](PRIVATE_WITNESS.md) handles the residual
single-challenge message comparison after these global conventions.
It does not assume that a modified accepted body contains a valid
sharing polynomial, and it does not condition an oracle or the
adversary on witness survival. Padding of the final label set and
the challenge support are proof devices, never protocol messages.
