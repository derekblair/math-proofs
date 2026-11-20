# Formalization Catalogue

Selected exported results in this repository, their verification status, and their
axiom dependencies. Statuses mirror the labeling convention in
[CONTENTS.md](CONTENTS.md).

| Theorem | File | Status | Axioms beyond Lean's standard ones | Paper |
|---|---|---|---|---|
| `es_covering_217mod264` (positive natural witnesses, denominator equations, and identity); `es_identity_217mod264` (rational equality) | [Mathproofs/ESIdentity.lean](Mathproofs/ESIdentity.lean) | [PROVED] | none | [ES-001](CONTENTS.md#es-001) |
| `es_crt_escape` (escape from explicit local obstructions; no polynomial-identity implication) | [Mathproofs/ESBarrier.lean](Mathproofs/ESBarrier.lean) | [PROVED] conditional kernel | none | [ES-002](CONTENTS.md#es-002) |
| `gap_sinh_superlinear`, `gap_sinh_le_mul_exp`, `gap_log_one_add_ge`, `six_pow_mul_factorial_le` | [Mathproofs/CollatzGapSinh.lean](Mathproofs/CollatzGapSinh.lean) | [PROVED] | none | preprint in preparation |
| `gap_delta_sign_criterion`, `gap_lt_of_delta_signs`, `gap_argmin_of_delta_signs` (including interval membership) | [Mathproofs/CollatzGapDelta.lean](Mathproofs/CollatzGapDelta.lean) | [PROVED] | none | preprint in preparation |
| `gapT_seconddiff_pos`, `gapS_seconddiff_pos`, `gapDelta_strictly_increasing`, `gap_margin_duality` (C18b convexity + C26 margin-duality trichotomy) | [Mathproofs/CollatzGapConvex.lean](Mathproofs/CollatzGapConvex.lean) | [PROVED] | none | preprint in preparation |
| `cf_error_formula`, `cf_ratio_formula`, `cf_det_identity` (complete-quotient API for irrationals) | [Mathproofs/CollatzGapCF.lean](Mathproofs/CollatzGapCF.lean) | [PROVED] | none | preprint in preparation |
| `cf_selector_le`, `cf_selector_lt`, `cf_selector_eq`, `cf_selector_ne` (C24 tail-mirror selector + strict dichotomy) | [Mathproofs/CollatzGapC24.lean](Mathproofs/CollatzGapC24.lean) | [PROVED] | none | preprint in preparation |
| `cf_firstdiff_decide`, `cf_firstdiff`, `cf_firstdiff_term` (C24 Lemma 3 finite first-difference) | [Mathproofs/CollatzGapC24Lemma3.lean](Mathproofs/CollatzGapC24Lemma3.lean) | [PROVED] | none | preprint in preparation |
| `strictConvexOn_sinh_Ici`, `sinh_scaling_gt`, `c23a` (C23 sinh key estimates + selector assembly) | [Mathproofs/CollatzGapC23.lean](Mathproofs/CollatzGapC23.lean) | [PROVED] | none | preprint in preparation |
| `c26a`, `c26b`, repaired `c26c`, `c22_delta_pos_at`, `c22_upper`, `c22_argmin`, `log_one_add_div_one_sub_ge` (C22/C25/C26 gap-factor batch) | [Mathproofs/CollatzGapC22C25.lean](Mathproofs/CollatzGapC22C25.lean) | [PROVED] | none | preprint in preparation |
| `c29`, `c29_strict` + `lemmaA_coprime`, `lemmaB_nowrap`, `yfrac_formula`, `count_le` (C29 discrepancy dominance) | [Mathproofs/CollatzGapC29.lean](Mathproofs/CollatzGapC29.lean) | [PROVED] | none | preprint in preparation |
| C29′ from-below mirror lemmas (`beta_pos`, `beta_irr`, `isStrictRecord_beta`) | [Mathproofs/CollatzGapC29Mirror.lean](Mathproofs/CollatzGapC29Mirror.lean) | [PROVED] | none | preprint in preparation |
| `lemma_X0`, `lemma_S1S3` (X0/S1S3 descent core) | [Mathproofs/ESX0S1S3.lean](Mathproofs/ESX0S1S3.lean) | [PROVED] | none | preprint in preparation |
| `mu_valuation_of_S3`, `transfer_key_00`, `transfer_qcancel` (general descent transfer) | [Mathproofs/ESDescentTransfer.lean](Mathproofs/ESDescentTransfer.lean) | [PROVED] | none | preprint in preparation |
| C64/C64b hump-law identity kernel + arithmetic closures (22 theorems) | [Mathproofs/CollatzGapHump.lean](Mathproofs/CollatzGapHump.lean) | [PROVED] | none | preprint in preparation |
| `ESQadicBranch1.qadic_type_restriction` (explicit QQ/M23/R74 inputs); `kill_02`, `kill_12`, `descent_01` | [Mathproofs/ESQadicBranch1.lean](Mathproofs/ESQadicBranch1.lean) | [CONDITIONAL] classification; [PROVED] arithmetic | none | preprint in preparation |
| `feasible_emit_noTri`, `feasible_emit_noC4`, `emittedGraph` (every feasible move on a distinct triple preserves girth ≥5); identity-score floor and conditional rigidity | [Mathproofs/Girth5Floor3v.lean](Mathproofs/Girth5Floor3v.lean) | [PROVED] local preservation | none | preprint in preparation |
| Five invalid moves rejected; two identity moves feasible | [Mathproofs/Girth5Floor3vRegression.lean](Mathproofs/Girth5Floor3vRegression.lean) | [PROVED] regressions | none | regression checks |
| `b0_vacuity`, `fiber_collision_law` (W(M) witness-complex kernel) | [Mathproofs/WitnessComplexThm2.lean](Mathproofs/WitnessComplexThm2.lean) | [PROVED] | none | preprint in preparation |
| `t2_integrality_iff`, `t3_full_class` + 5 more (W(M) Thm 1(a) + Thm 3) | [Mathproofs/WitnessComplexThm13.lean](Mathproofs/WitnessComplexThm13.lean) | [PROVED] | none | preprint in preparation |
| `t2_jacobi_neg_one`, `t2_class_nonsquare` (T2 prime-square obstruction) | [Mathproofs/ESPrimeSquareT2.lean](Mathproofs/ESPrimeSquareT2.lean) | [PROVED] | none | preprint in preparation |
| `t1_two_case` (T1 x²≡−f unsolvability, two-case reciprocity) | [Mathproofs/EST1TwoCase.lean](Mathproofs/EST1TwoCase.lean) | [PROVED] | none | preprint in preparation |
| `qr_core_t2_misses`, `qr_core_t1_misses` (QR-core missed by T1∪T2) | [Mathproofs/ESQRCore.lean](Mathproofs/ESQRCore.lean) | [PROVED] | none | preprint in preparation |
| `qr_core_count` (product count); `residueCRT`, `targetCRTEquiv`, `qrCRTEquiv`, `qr_residue_count` (actual unit/1-mod24 residues and their square subset) | [Mathproofs/ESQRCoreCount.lean](Mathproofs/ESQRCoreCount.lean) | [PROVED] product and actual residue counts | none | preprint in preparation |
| `t1_five_covers_class`, `t2_seven_covers_class`, `t1_w20_class_covered`, `qnr7_covered` (positive natural covering from 5/7 forcing) | [Mathproofs/ESFiveSevenForcing.lean](Mathproofs/ESFiveSevenForcing.lean) | [PROVED] | none | preprint in preparation |
| `branch_sdr_endgame`, `branch_sdr_endgame_clique_bound` (SDR endgame, pair-specific conditional) | [Mathproofs/ESBranchSDREndgame.lean](Mathproofs/ESBranchSDREndgame.lean) | [PROVED] | none | preprint in preparation |
| `fam1_covers`, `fam2_covers`, `fam3_covers` (full positive-natural covering); arithmetic families and fiber pinning | [Mathproofs/ESMod7UniversalFamilies.lean](Mathproofs/ESMod7UniversalFamilies.lean) | [PROVED] | none | preprint in preparation |
| `fiber_compat_pair_iff`, `fiber_compat_saturated`, `fiber_compat_card`, `forced_digit` (+ unit/digit API) | [Mathproofs/ESFiberCompat.lean](Mathproofs/ESFiberCompat.lean) | [PROVED] | none | [ES-004](CONTENTS.md#es-004) |
| `fiber_compat_iffC`, `forced_digit_of_memC` (+ composite digit/projection API) | [Mathproofs/ESFiberCompatComposite.lean](Mathproofs/ESFiberCompatComposite.lean) | [PROVED] | none | [ES-004](CONTENTS.md#es-004) |
| `liveUnion_bound_6`, `liveUnion_bound_11`, 16 BLOCKED-shape `decide` theorems | [Mathproofs/ESFiberTiling.lean](Mathproofs/ESFiberTiling.lean) | [PROVED] | none | [ES-004](CONTENTS.md#es-004) |
| `demands_descend`, `capability_descend`, `kappa_*`, `digitMap_*`, `degeneracy_lemma` | [Mathproofs/CompositeSuppression.lean](Mathproofs/CompositeSuppression.lean) | [PROVED] | none | [ES-004](CONTENTS.md#es-004) |
| `branch2_collapse`, `family_identity`, `branch2_m_mod8_refuted` | [Mathproofs/ESBranchTwo.lean](Mathproofs/ESBranchTwo.lean) | [PROVED] | none | [ES-004](CONTENTS.md#es-004) |
| `crt44_*`, `sixClasses_exact`, `sixClasses_inv_closed`, `crt_unique_one`, `crt_inv_compose`, `S1_subset`, `S1_proj_subset`, `S1_exact` (kernel proofs; no native certificates) | [Mathproofs/ESRefinedSieveInverse.lean](Mathproofs/ESRefinedSieveInverse.lean) | [PROVED] | none | [ES-006](CONTENTS.md#es-006) |
| `uBranch_isolation`, `closeImage_disjoint_of_subset`, `uSide_degree_bound`, `r163_uSideBound_inHclique` | [Mathproofs/ESUBranchIsolation.lean](Mathproofs/ESUBranchIsolation.lean) | [PROVED] | none | [ES-006](CONTENTS.md#es-006) |
| `t2_iff`, `t5_saturation`, `t5_double_saturation`, `dichotomy_two_margins` | [Mathproofs/HoleSuppression.lean](Mathproofs/HoleSuppression.lean) | [PROVED] | none | [SS-002](CONTENTS.md#ss-002) |
| `t5prime_R1/R2/R3/R6`, `t5prime_combined` | [Mathproofs/AbsorbedRegime.lean](Mathproofs/AbsorbedRegime.lean) | [PROVED] | none | [SS-002](CONTENTS.md#ss-002) |
| `t4_self_bound` (corrected R200 T4) | [Mathproofs/AbsorbedBound.lean](Mathproofs/AbsorbedBound.lean) | [PROVED] | none | [SS-002](CONTENTS.md#ss-002) |
| `rawBlocked_translate`, `rigidity`, `march`, `march_neg`, `march_saturated_iff_shadow`, `plateau_downward` | [Mathproofs/TranslationMarch.lean](Mathproofs/TranslationMarch.lean) | [PROVED] | none | [SS-003](CONTENTS.md#ss-003) |
| `psi_as_phi_translate`, `feas_iff`, `chain_bounds`, `chain_width` | [Mathproofs/CorrectedMarch.lean](Mathproofs/CorrectedMarch.lean) | [PROVED] | none | [SS-003](CONTENTS.md#ss-003) |
| `march_unsat_pos/neg`, `propagation_subset`, `rescue_threshold_pos/neg`, `additive_bound_pos/neg` | [Mathproofs/TranslationMarchUnsat.lean](Mathproofs/TranslationMarchUnsat.lean) | [PROVED] | none | [SS-003](CONTENTS.md#ss-003) |
| `hole_twin_of_dip`, `chain_dip`, `s1_instance` | [Mathproofs/HoleTwinDip.lean](Mathproofs/HoleTwinDip.lean) | [PROVED] | none | [SS-003](CONTENTS.md#ss-003) |
| `sliding_window_up/down`, `continuation_iff`, `break_case`, `reset_case`, `perfect_case`, `phi_duality` | [Mathproofs/DipMarch.lean](Mathproofs/DipMarch.lean) | [PROVED] | none | [SS-003](CONTENTS.md#ss-003) |
| `generalized_subfamily_identity` [PROVED]; `admission_criterion`, `a0_constancy`, `u_eq_Aqe_div_f`, `excess_prime_dvd_u`, `M_const`, `split_layered_repaired` [PROVED*] | [Mathproofs/ESSubfamilyExtended.lean](Mathproofs/ESSubfamilyExtended.lean) | [PROVED] / [PROVED*] | none | [SS-004](CONTENTS.md#ss-004) |
| `theorem6`, `catalog_ceiling` (+ one-sided/binding variants) | [Mathproofs/MarchLadderCeiling.lean](Mathproofs/MarchLadderCeiling.lean) | [PROVED] | none | [SS-004](CONTENTS.md#ss-004) |
| `A3_holds`, `no_forcing_equality/disjoint/sharing` (+ transfer API) | [Mathproofs/SigmaTrans.lean](Mathproofs/SigmaTrans.lean) | [PROVED] | none | [SS-005](CONTENTS.md#ss-005) |
| `fiber_overlap`, `fiber_overlap_identity`, `autocorr_le_one`, `top_interval_sparsity` | [Mathproofs/FiberOverlap.lean](Mathproofs/FiberOverlap.lean) | [PROVED] | none | [SS-005](CONTENTS.md#ss-005) |
| `consecT_gives_consec_fire`, `no_consecT_scattered`, `consec_window_no_consecT_not_full`, `full_no_consecT_gap_window`, `sharpness_witness` | [Mathproofs/AbstractLock.lean](Mathproofs/AbstractLock.lean) | [PROVED] | none | [SS-006](CONTENTS.md#ss-006) |
| `no_dual_target_demote`, `no_dual_source_promote`, `dual_preserves_s_card`, `ascentDepth_*` | [Mathproofs/TransDAG.lean](Mathproofs/TransDAG.lean) | [PROVED] | none | [SS-006](CONTENTS.md#ss-006) |
| `V1_void_iff_zero` … `V8_forced_split`, `k0_zero_impossible` | [Mathproofs/VoidUnion.lean](Mathproofs/VoidUnion.lean) | [PROVED] | none | [SS-007](CONTENTS.md#ss-007) |
| `forced_cell_in_window`, `void_exclusion` | [Mathproofs/VoidLock.lean](Mathproofs/VoidLock.lean) | [PROVED] | none | [SS-007](CONTENTS.md#ss-007) |
| `additive_iff_disjoint` (P1), `defect_core` (P2i), `fully_additive_submonoid` (P2ii), `disjoint_footprint_submonoid` (P2iii-a), `Phi_*`/`Rho_*` (T1/T1′), `prod_additive_iff` (T2) — build dependency of VoidMonoid/VoidDefectHom | [Mathproofs/VoidMonoidParam.lean](Mathproofs/VoidMonoidParam.lean) | [PROVED*] (staged, build-clean) | none | [SS-007](CONTENTS.md#ss-007) |
| `d2c_not_closed`, `d2c_generated_loses_disjoint`, `maximal_family_tiles` | [Mathproofs/VoidMonoid.lean](Mathproofs/VoidMonoid.lean) | [PROVED] | none | [SS-007](CONTENTS.md#ss-007) |
| `defect_hom_rigidity` (H1), `literal_product_never` (C1), `split_boundary_witness` (C2), `mixed_count` (C4) | [Mathproofs/VoidDefectHom.lean](Mathproofs/VoidDefectHom.lean) | [PROVED] | none | [SS-007](CONTENTS.md#ss-007) |
| `absorp_refl/trans/antisymm`, `datum_eq_of_absorpLE`, `absorp_datum_iff`, `rho_superadd_disjoint/general`, `overlap_deficit_bound`, `rho_absorption_collapse`, `absorption_collapse_unique_core`, `singleton_factorization` | [Mathproofs/ESAbsorptionOrder.lean](Mathproofs/ESAbsorptionOrder.lean) | [PROVED] with `G.C.Nonempty` for the datum equivalence, `H.C.Nonempty` for collapse/minimum-core uniqueness of distinct `G ≼ H`, and no singleton on `S0` within a finite ambient family `𝒢 ⊇ S` | none | [ES-005](CONTENTS.md#es-005) |
| `s2a'_forced`, `s2b_pc`, `s2c_void`, `s2d_split`, `spectrum_partition`, `psi_union_max` | [Mathproofs/ESForcingSpectrum.lean](Mathproofs/ESForcingSpectrum.lean) | [PROVED] | none | [ES-005](CONTENTS.md#es-005) |
| `theoremA_crt`, `theoremB_scaling`, `theoremC_filter`, `theoremD_card` | [Mathproofs/ESForcingDecomp.lean](Mathproofs/ESForcingDecomp.lean) | [PROVED] | none | [ES-005](CONTENTS.md#es-005) |
| `SidonSat184.r47_sat184` (nine elements, interval membership, Sidon property, maximality); `unique_extension_saturated` | [Mathproofs/SidonSat184.lean](Mathproofs/SidonSat184.lean) | [PROVED] | none | [SS-001](CONTENTS.md#ss-001) |

| `covered_classes_exact`, `parent_fiber_card`, `covered_parent_fiber_card`, `covered_class_identity` | [Mathproofs/ESIdentityCRT.lean](Mathproofs/ESIdentityCRT.lean) | [PROVED] six subclasses and one-out-of-eleven residue count | none | [ES-001](CONTENTS.md#es-001) |
| `of_split`, `splitting_family`, `of_t2` (positive-natural covering constructors) | [Mathproofs/ESCovering.lean](Mathproofs/ESCovering.lean) | [PROVED] | none | preprint in preparation |
| `emitted_edgeCount_balance`, `score_le_D_of_extremal`, `three_v_rigidity_of_extremal`, `three_v_gap_of_extremal` | [Mathproofs/Girth5Extremal.lean](Mathproofs/Girth5Extremal.lean) | [PROVED] from global edge maximality | none | preprint in preparation |
| `census_facts`, `census_unique_hole`, `census_blocked_card`, `census_extensions_saturated`, `census_gate_counterexamples` | [Mathproofs/SidonSat184Census.lean](Mathproofs/SidonSat184Census.lean) | [PROVED] nine displayed rows and C28 witnesses | none | [SS-001](CONTENTS.md#ss-001) |

| `factor_pos`, `log_factor`, `log_factor_diff`, `c22_factor_unique_min` | [Mathproofs/CollatzGapFactor.lean](Mathproofs/CollatzGapFactor.lean) | [PROVED] explicit analytic factor under C22 hypotheses | none | preprint in preparation |
| `qadic_type_bounds_without_sweep`, `qadic_type_restriction_from_m23`, `generic_type01_counterexample` | [Mathproofs/ESQadicBoundary.lean](Mathproofs/ESQadicBoundary.lean) | [PROVED] arithmetic boundary; three-type classification still conditional on R74 | none | preprint in preparation |

| `branch2_covering_of_divisibility`, `transfer_00_covering`, `transfer_11_covering` | [Mathproofs/ESDescentCovering.lean](Mathproofs/ESDescentCovering.lean) | [PROVED] positive parent-progression identities from explicit slope/intercept data | none | preprint in preparation |

## Scope limits

The Collatz rows describe analytic/CF kernels and conditional assemblies,
not a completed specialization to log₂3 or Collatz dynamics. Positive-natural
covering is now proved for the stated mod-7 and 5/7 families. The QR count has
a proved CRT interpretation for its explicitly defined target set; externally
filtered frontiers and cubic-family exclusions remain separate. Descent and
q-adic results still require the stated QQ/M23/R74 inputs where used. The
barrier is a CRT escape kernel with supplied local obstructions; the integer
polynomial Schinzel–Mordell implication remains unformalized. Global graph
extremality now implies the score ceiling through exact edge accounting.

## Checking instructions

Requires [elan](https://github.com/leanprover/elan) (the Lean toolchain manager)
and Lean 4.34.1 + Mathlib v4.34.1 (pinned by `lean-toolchain` and
`lake-manifest.json`):

```bash
lake exe cache get   # fetch precompiled Mathlib oleans (large download)
lake build           # builds all of Mathproofs
```

CI (`.github/workflows/lean_action_ci.yml`) runs the full build on every push.
`#print axioms <theorem>` on any entry above reproduces the axiom column;
nothing here is claimed on the basis of a `sorry`.

## Formalizations in progress (not yet published)

The following local formalizations are still being worked through the
publication pipeline — they are **not** part of this release:

- `ESCubicClassify.lean` (R89, quarantined — known `Int.Coprime` breakage, not registered)
- `DonorKernel.lean`, `ESUBBranchIsolation.lean`
  (verification status ambiguous or in flight — excluded pending confirmation)

## SS-004 verification checkpoint (issue #10)

The six staged results `admission_criterion`, `a0_constancy`, `u_eq_Aqe_div_f`,
`excess_prime_dvd_u`, `M_const`, and `split_layered_repaired` passed compiled-statement/
axiom checks and `leanchecker --verbose Mathproofs.ESSubfamilyExtended` (exit 0) at
commit `c9d3c0ebb6474c5b134b2c85cae36ff84cd2af43`, using Lean 4.34.1 (compiler
`5045d0056413266e57c625dcd7c365b10e377c52`) and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. `u_eq_Aqe_div_f` reports only
`propext`; the other five report `propext`, `Classical.choice`, and `Quot.sound`.
No `sorryAx` or nonstandard axioms were reported in these checks.
See [the recorded SS-004 audit](https://github.com/derekblair/math-proofs/issues/10#issuecomment-6405779931).

The earlier full-build resource blocker in `Mathproofs/SidonSat184Census.lean`
is resolved. The repaired local checkout completed all 17,966 build jobs (exit 0),
followed by the census artifact axiom audit and official kernel replay (exit 0).
Both [push CI](https://github.com/derekblair/math-proofs/actions/runs/40426034024)
and [PR CI](https://github.com/derekblair/math-proofs/actions/runs/40426098547)
also completed the 17,966-job build successfully for repair head
`cbf4c3d4b3ed545daf22b1e00a28a68b48e8867a`. Those CI workflows skipped their
optional axiom-audit/kernel-replay steps; the separate local audit evidence
must not be conflated with CI.

[Source-repair PR #15](https://github.com/derekblair/math-proofs/pull/15) merged
at `0b17820a79f969c883b363de670402512b47341d` on 2026-10-27 at 00:55:28 UTC.
The [coordinator's report](https://github.com/derekblair/math-proofs/issues/10#issuecomment-6431013776)
attests an independent hostile-review PASS for the census repair, with unchanged
exported census statements and rows. This is coordinator-attested external review,
not a GitHub review submission or independent review of the six SS-004 results.
`ESSubfamilyExtended.lean` is byte-identical between the audited commit above and
the repair merge commit.

The existing [PROVED*] labels remain staged pending the relevant independent
SS-004/status-promotion and documentation review. The full-build/source-delivery
blocker is no longer open, but its resolution does not by itself settle those
review gates or close [issue #10](https://github.com/derekblair/math-proofs/issues/10).
No additional theorem is promoted by this checkpoint.
