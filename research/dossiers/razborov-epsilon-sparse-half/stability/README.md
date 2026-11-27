# Finite edit stability for two endpoint templates

`StabilityExamples.lean` proves `SparseHalfStability.petersen_edit_stability` and `SparseHalfStability.c5_edit_stability`: if a finite triangle-free graph has sufficiently small directed edit distance to the indicated labeled template and all original fibers are adequately large, there is a fractional half with unordered cost at most 1/50. The directed-error threshold is (n/10^7)^2 and minimum original fiber ratios are 0.099 for Petersen or 0.199 for C5. `StabilityDirected.lean` identifies the directed count with twice ordinary unordered edits.

The proof formalizes the weighted template banks and the reclassification, codegree and disturbed-matching transfer from Norin–Yepremyan. Requires pinned Lean 4.34.1 and Mathlib. The proof is local, not the limit rigidity or final edit assignment.
