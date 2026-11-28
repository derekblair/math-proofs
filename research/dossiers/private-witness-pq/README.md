# Private-witness security reduction for an experimental PQ envelope

The [paper argument](PRIVATE_WITNESS.md) replaces a public support
catalog with a private proof coin. This changes the security reduction,
not the encryption scheme. The model and assumptions are specified
in [MODEL.md](MODEL.md). This is not a new KEM, security certification,
deployment recommendation, or claimed speedup over standardized schemes.

At n=130 sites, c=63 disclosed domains, and f=6 outages, the two-family
component reduction multiplier is about 3,401 rather than 130,984 for
the public 4,678-support comparison. The wire format in this comparison
is unchanged; the one-block receiver selects 124 decapsulations per
family instead of 88 for the different public-portfolio layout.
These are different decoding layouts; the private witness itself
does not change an existing one-block decoder.

The Lean files verify finite combinatorial ingredients only:
- `BlindWitness.lean`: weighted transcript and uniform hidden support
  factor, assuming the product law implemented by the real experiment.
- `HittingAlteration.lean`, `CatalogBound.lean`: the finite
  [explicit-catalog lower bound](CATALOGUE_BOUND.md), an application
  of classical transversal alteration, not a new combinatorial method.

Reproduce the exact local arithmetic with `python3 checks.py`, and
replay Lean with the pinned Lean/Mathlib 4.34.1 using `bash replay.sh`.
[REPLAY.txt](REPLAY.txt) lists what was checked. The proof's KEM,
guard, PRF, and oracle assumptions were reviewed on paper and are
not formalized end-to-end.

The named 4,678-support baseline is independently reproducible from its
three small [catalogues and check](baseline/). Nothing here claims that
baseline is optimal. Secret-guessing and artificial abort are established
proof techniques, not claimed as new tools; see for comparison the
[adaptive-security subset guessing in the APKE proof](https://eprint.iacr.org/2022/619.pdf).

## Same ciphertext size and same decoder budget

The [cluster minimax addendum](cluster/PRIVATE_CLUSTERS.md) retains
the previous 130-site wire budget and 88 selected decapsulations per
family. The best fixed disjoint layout under those caps gives a proof
multiplier of about 13,818 instead of 130,984 for the explicit public
catalogue baseline. Leaving that baseline layout itself unchanged
gives about 14,059. The one-block 3,401 point above uses more
decapsulations and is not the same-budget comparison.

The addendum proves optimality for the specified fixed disjoint
layout and private fixed-coordinate support game. It does not prove a
general cryptographic lower bound. Lean checks the supporting-slope
and probability-scaling identities, not the entire reduction or layout
certificate. See [cluster replay](cluster/REPLAY.txt).

## Two-level layout, same wire and fewer decapsulations

The [nested construction and reduction](nested/TWO_LEVEL_WITNESS.md)
uses the same 130 capsules per family and models the same 63 adaptive
domain disclosures and six outages. The asymmetric option needs at most
85 selected decapsulations per family instead of 88, and lowers the
two-family proof multiplier from about 13,818 to 6,898. The symmetric
option needs 84, with a larger multiplier of about 8,839.

[Lean](nested/lean/REPLAY.md) checks the asymmetric exact-63 bound for
all labelled exposure allocations and the two attaining examples. The
security reduction and padding to the disclosure cap are paper
arguments under the stated model. These are not timings and do not
establish a new KEM or a deployment claim.

## Native ciphertext under a different custody model

The [native-custody comparison](native-custody/NATIVE_THRESHOLD_RAMP.md)
keeps the 1,088-byte ML-KEM-768 ciphertext and uses 255 bytes of
custodian responses for the stated ramp-sharing setup. This needs a trusted
volatile combiner, which holds the reusable seed during each evaluation.
It is not an improvement under the original combiner-snapshot model.
Lean checks the conditional integer response bound; security and
snapshot separation are idealized paper arguments. No new KEM,
deployment, or measured performance.
