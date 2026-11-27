# Exact nonlinear refresh: entropy bounds and circuit sampling

In the [ideal two-epoch diagonal model](../README.md), an arbitrary exact
sampler over F_(2^r) with 2m sites and even m needs entropy at least
log₂(q ceil(m/r)). This strengthens the earlier Shannon bound to the
same numerical value as the support lower bound, and is sharp when
r≥m−1 (where the site capacity requirement holds).

[Unordered, anchored circuit sampling](ANCHORED-CIRCUIT.md) saves
Θ(r log r) bits of entropy over independent ordered site draws when
r is proportional to log n. At n=256 and q=512, its exact distribution
has entropy about 62.2552 bits, versus the exact fixed 72-bit ordered
sampler. This is an entropy comparison, not a claim of a fixed-length
62-bit fair seed. Gottlieb's classical incidence-rank theorem gives
optimality within the specified fixed-anchor architecture.

[The unanchored sparse-circuit bound](MONO-CUT.md) shows that dropping the
fixed anchor but keeping basis-labelled circuits and independent scalar
mixing cannot reduce the leading Θ(log² n) entropy order. The gap for
unconstrained nonlinear exact samplers remains open.

## Reproducibility and limits

The finite-mass probability inequalities, including the Shannon
consequence conditional on the top-mass cap, check with Lean 4.34.1
and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. Run with LEAN_PATH
pointing to the compiled Mathlib and the present directory, in order:

    lean -o RefreshCollisionEntropy.olean RefreshCollisionEntropy.lean
    lean -o RefreshCollisionTop.olean RefreshCollisionTop.lean
    lean -o RefreshCollisionShannon.olean RefreshCollisionShannon.lean
    lean -o RefreshCollisionLower.olean RefreshCollisionLower.lean

The final axiom list is propext, Classical.choice, Quot.sound. The
combinatorial derivation of the cap, the two circuit results, and the
site-to-polynomial model are written proofs, not part of this Lean
check. The two Python scripts provide separate exact finite controls.
This is not a key encapsulation mechanism or implementation claim.
