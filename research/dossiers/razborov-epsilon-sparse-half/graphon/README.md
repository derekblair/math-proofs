# Verified graphon ingredients

Sixteen new modules clean-replayed under the same Lean 4.34.1 and pinned Mathlib as the parent dossier. All printed axiom reports contain only propext, Classical.choice, and Quot.sound.

- GraphonCaseTwo.graphon_case_two proves the strict weighted Case 2 theorem at the exact endpoint on any finite measure space. It constructs the fractional half explicitly, derives its cost from the triangle-free hypothesis, and averages using checked Fubini marginal identities. The input mark and residual allocation may both be fractional.
- GraphonMantel checks exact weighted Mantel from zero triangle integral, also after reweighting. ComplementRowsAE shows that saturated rows along a positive outside edge are complementary indicators. IndependentRowsAE proves zero internal energy of the weighted neighborhood allocation.
- HalfCutContinuity.cut_beta gives the fractional half optimum a Lipschitz factor of 1/2 in aligned cut norm. TriangleCutContinuity checks the factor-three triangle counting bound. CutBinaryTemplate checks the finite binary template cut-to-L1 transfer. KernelPullback checks product energy and triangle density pushforward/pullback.
- Remaining paper steps: existence of the marked cut limit, decomposition into its countably many positive complementary atoms, selecting the new balanced allocations and finishing equality/edit-stability and the finite-graph transfer. This still is not an end-to-end Lean proof of Razborov’s epsilon question.

Replay with MATHLIB_LEAN_PATH and LEAN_BIN set as in the main dossier and run bash replay-graphon.sh. No cache artifacts are required in this directory.

## Marked compactness extension

`MarkedGraphonCompactness.lean` provides the complete marked compactness theorem on varying finite-measure spaces with total mass one. The proof constructs finite padded weak-regularity towers, extracts coherent limit tables, realizes a nested interval kernel, then aligns the original kernels and marks by explicit min-mass couplings. See `AlignedLimits.lean` for numerical transfer of triangle density and fractional-half energy. The original specialized Case 2 replay remains available; the full 54-module replay is `replay-compactness.sh`. Use the same pinned Lean and Mathlib search paths (including all package paths) indicated above.
