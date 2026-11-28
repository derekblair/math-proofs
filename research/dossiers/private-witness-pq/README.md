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
