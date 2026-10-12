# Formalization Catalogue

Every theorem formalized in this repository, its verification status, and its
axiom dependencies. Statuses mirror the labeling convention in
[CONTENTS.md](CONTENTS.md).

| Theorem | File | Status | Axioms beyond Lean's standard ones | Paper |
|---|---|---|---|---|
| `es_identity_217mod264` | [Mathproofs/ESIdentity.lean](Mathproofs/ESIdentity.lean) | [PROVED] | none | [ES-001](CONTENTS.md#es-001) |
| `es_barrier` | [Mathproofs/ESBarrier.lean](Mathproofs/ESBarrier.lean) | [PROVED*] | `schinzel_mordell`, `dirichlet_arith_prog` | [ES-002](CONTENTS.md#es-002) |
| `gap_sinh_superlinear`, `gap_sinh_le_mul_exp`, `gap_log_one_add_ge`, `six_pow_mul_factorial_le` | [Mathproofs/CollatzGapSinh.lean](Mathproofs/CollatzGapSinh.lean) | [PROVED] | none | preprint in preparation |
| Δ-sign machinery for the Collatz gap-factor argmin theorems (C22/C23/C25/C26) — structural definitions and lemmas, a build dependency of `CollatzGapConvex` | [Mathproofs/CollatzGapDelta.lean](Mathproofs/CollatzGapDelta.lean) | supporting definitions | none | preprint in preparation |
| `gapT_seconddiff_pos`, `gapS_seconddiff_pos`, `gapDelta_strictly_increasing`, `gap_margin_duality` (C18b convexity + C26 margin-duality trichotomy) | [Mathproofs/CollatzGapConvex.lean](Mathproofs/CollatzGapConvex.lean) | [PROVED] | none | preprint in preparation |
| `cf_error_formula`, `cf_ratio_formula`, `cf_det_identity` (complete-quotient API for irrationals) | [Mathproofs/CollatzGapCF.lean](Mathproofs/CollatzGapCF.lean) | [PROVED] | none | preprint in preparation |
| `cf_selector_le`, `cf_selector_lt`, `cf_selector_eq`, `cf_selector_ne` (C24 tail-mirror selector + strict dichotomy) | [Mathproofs/CollatzGapC24.lean](Mathproofs/CollatzGapC24.lean) | [PROVED] | none | preprint in preparation |
| `cf_firstdiff_decide`, `cf_firstdiff`, `cf_firstdiff_term` (C24 Lemma 3 finite first-difference) | [Mathproofs/CollatzGapC24Lemma3.lean](Mathproofs/CollatzGapC24Lemma3.lean) | [PROVED] | none | preprint in preparation |
| `strictConvexOn_sinh_Ici`, `sinh_scaling_gt`, `c23a` (C23 sinh key estimates + selector assembly) | [Mathproofs/CollatzGapC23.lean](Mathproofs/CollatzGapC23.lean) | [PROVED] | none | preprint in preparation |
| `c26a`, `c26b`, `c26c`, `c22_delta_pos_at`, `log_one_add_div_one_sub_ge` (C22/C25/C26 gap-factor batch) | [Mathproofs/CollatzGapC22C25.lean](Mathproofs/CollatzGapC22C25.lean) | [PROVED] | none | preprint in preparation |
| `c29` + `lemmaA_coprime`, `lemmaB_nowrap`, `yfrac_formula`, `count_le` (C29 discrepancy dominance) | [Mathproofs/CollatzGapC29.lean](Mathproofs/CollatzGapC29.lean) | [PROVED] | none | preprint in preparation |
| C29′ from-below mirror lemmas (`beta_pos`, `beta_irr`, `isStrictRecord_beta`) | [Mathproofs/CollatzGapC29Mirror.lean](Mathproofs/CollatzGapC29Mirror.lean) | [PROVED] | none | preprint in preparation |
| `lemma_X0`, `lemma_S1S3` (X0/S1S3 descent core) | [Mathproofs/ESX0S1S3.lean](Mathproofs/ESX0S1S3.lean) | [PROVED] | none | preprint in preparation |
| `mu_valuation_of_S3`, `transfer_key_00`, `transfer_qcancel` (general descent transfer) | [Mathproofs/ESDescentTransfer.lean](Mathproofs/ESDescentTransfer.lean) | [PROVED] | none | preprint in preparation |
| C64/C64b hump-law identity kernel + arithmetic closures (22 theorems) | [Mathproofs/CollatzGapHump.lean](Mathproofs/CollatzGapHump.lean) | [PROVED] | none | preprint in preparation |
| Branch-1 q-adic type theorem (`kill_02`, `kill_12`, `descent_01`) | [Mathproofs/ESQadicBranch1.lean](Mathproofs/ESQadicBranch1.lean) | [PROVED] | none | preprint in preparation |
| Girth-5 3v floor theorem §B.1 (9 theorems: re-attachment model + cross-edge harmlessness) | [Mathproofs/Girth5Floor3v.lean](Mathproofs/Girth5Floor3v.lean) | [PROVED] | none | preprint in preparation |
| `b0_vacuity`, `fiber_collision_law` (W(M) witness-complex kernel) | [Mathproofs/WitnessComplexThm2.lean](Mathproofs/WitnessComplexThm2.lean) | [PROVED] | none | preprint in preparation |
| `t2_integrality_iff`, `t3_full_class` + 5 more (W(M) Thm 1(a) + Thm 3) | [Mathproofs/WitnessComplexThm13.lean](Mathproofs/WitnessComplexThm13.lean) | [PROVED] | none | preprint in preparation |
| `t2_jacobi_neg_one`, `t2_class_nonsquare` (T2 prime-square obstruction) | [Mathproofs/ESPrimeSquareT2.lean](Mathproofs/ESPrimeSquareT2.lean) | [PROVED] | none | preprint in preparation |
| `t1_two_case` (T1 x²≡−f unsolvability, two-case reciprocity) | [Mathproofs/EST1TwoCase.lean](Mathproofs/EST1TwoCase.lean) | [PROVED] | none | preprint in preparation |
| `qr_core_t2_misses`, `qr_core_t1_misses` (QR-core missed by T1∪T2) | [Mathproofs/ESQRCore.lean](Mathproofs/ESQRCore.lean) | [PROVED] | none | preprint in preparation |
| `\|Q\| = \|S\|/2^k` (QR-core exact count, CRT) | [Mathproofs/ESQRCoreCount.lean](Mathproofs/ESQRCoreCount.lean) | [PROVED] | none | preprint in preparation |
| 5/7-forcing lemma | [Mathproofs/ESFiveSevenForcing.lean](Mathproofs/ESFiveSevenForcing.lean) | [PROVED] | none | preprint in preparation |
| `branch_sdr_endgame`, `branch_sdr_endgame_clique_bound` (SDR endgame, pair-specific conditional) | [Mathproofs/ESBranchSDREndgame.lean](Mathproofs/ESBranchSDREndgame.lean) | [PROVED] | none | preprint in preparation |
| 18 theorems: three mod-7 universal families + fiber-pinning lemma | [Mathproofs/ESMod7UniversalFamilies.lean](Mathproofs/ESMod7UniversalFamilies.lean) | [PROVED] | none | preprint in preparation |

| `fiber_compat_pair_iff`, `fiber_compat_saturated`, `fiber_compat_card`, `forced_digit` (+ unit/digit API) | [Mathproofs/ESFiberCompat.lean](Mathproofs/ESFiberCompat.lean) | [PROVED] | none | [ES-004](CONTENTS.md#es-004) |
| `fiber_compat_iffC`, `forced_digit_of_memC` (+ composite digit/projection API) | [Mathproofs/ESFiberCompatComposite.lean](Mathproofs/ESFiberCompatComposite.lean) | [PROVED] | none | [ES-004](CONTENTS.md#es-004) |
| `liveUnion_bound_6`, `liveUnion_bound_11`, 16 BLOCKED-shape `decide` theorems | [Mathproofs/ESFiberTiling.lean](Mathproofs/ESFiberTiling.lean) | [PROVED] | none | [ES-004](CONTENTS.md#es-004) |
| `demands_descend`, `capability_descend`, `kappa_*`, `digitMap_*`, `degeneracy_lemma` | [Mathproofs/CompositeSuppression.lean](Mathproofs/CompositeSuppression.lean) | [PROVED] | none | [ES-004](CONTENTS.md#es-004) |
| `branch2_collapse`, `family_identity`, `branch2_m_mod8_refuted` | [Mathproofs/ESBranchTwo.lean](Mathproofs/ESBranchTwo.lean) | [PROVED] | none | [ES-004](CONTENTS.md#es-004) |
| `crt44_forward`, `crt44_backward`, `crt44_iff` [PROVED]; `sixClasses_inv_closed`, `crt_inv_compose`, `S1_subset` [PROVED*] | [Mathproofs/ESRefinedSieveInverse.lean](Mathproofs/ESRefinedSieveInverse.lean) | [PROVED] / [PROVED*] | `propext`, `Quot.sound` on crt44_*; +`native_decide` certs on the three [PROVED*] | [ES-006](CONTENTS.md#es-006) |
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
| `theorem6`, `catalog_ceiling` (+ one-sided/binding variants) | [Mathproofs/MarchLadderCeiling.lean](Mathproofs/MarchLadderCeiling.lean) | [PROVED] | `propext`, `Quot.sound` | [SS-004](CONTENTS.md#ss-004) |
| `A3_holds`, `no_forcing_equality/disjoint/sharing` (+ transfer API) | [Mathproofs/SigmaTrans.lean](Mathproofs/SigmaTrans.lean) | [PROVED] | none | [SS-005](CONTENTS.md#ss-005) |
| `fiber_overlap`, `fiber_overlap_identity`, `autocorr_le_one`, `top_interval_sparsity` | [Mathproofs/FiberOverlap.lean](Mathproofs/FiberOverlap.lean) | [PROVED] | none | [SS-005](CONTENTS.md#ss-005) |
| `consecT_gives_consec_fire`, `no_consecT_scattered`, `consec_window_no_consecT_not_full`, `full_no_consecT_gap_window`, `sharpness_witness` | [Mathproofs/AbstractLock.lean](Mathproofs/AbstractLock.lean) | [PROVED] | none | [SS-006](CONTENTS.md#ss-006) |
| `no_dual_target_demote`, `no_dual_source_promote`, `dual_preserves_s_card`, `ascentDepth_*` | [Mathproofs/TransDAG.lean](Mathproofs/TransDAG.lean) | [PROVED] | none | [SS-006](CONTENTS.md#ss-006) |
| `V1_void_iff_zero` … `V8_forced_split`, `k0_zero_impossible` | [Mathproofs/VoidUnion.lean](Mathproofs/VoidUnion.lean) | [PROVED] | none | [SS-007](CONTENTS.md#ss-007) |
| `forced_cell_in_window`, `void_exclusion` | [Mathproofs/VoidLock.lean](Mathproofs/VoidLock.lean) | [PROVED] | none | [SS-007](CONTENTS.md#ss-007) |
| `additive_iff_disjoint` (P1), `defect_core` (P2i), `fully_additive_submonoid` (P2ii), `disjoint_footprint_submonoid` (P2iii-a), `Phi_*`/`Rho_*` (T1/T1′), `prod_additive_iff` (T2) — build dependency of VoidMonoid/VoidDefectHom | [Mathproofs/VoidMonoidParam.lean](Mathproofs/VoidMonoidParam.lean) | [PROVED*] (staged, build-clean) | none | [SS-007](CONTENTS.md#ss-007) |
| `d2c_not_closed`, `d2c_generated_loses_disjoint`, `maximal_family_tiles` | [Mathproofs/VoidMonoid.lean](Mathproofs/VoidMonoid.lean) | [PROVED] | none | [SS-007](CONTENTS.md#ss-007) |
| `defect_hom_rigidity` (H1), `literal_product_never` (C1), `split_boundary_witness` (C2), `mixed_count` (C4) | [Mathproofs/VoidDefectHom.lean](Mathproofs/VoidDefectHom.lean) | [PROVED] | none | [SS-007](CONTENTS.md#ss-007) |
| `absorp_refl/trans/antisymm`, `absorp_datum_iff`, `rho_superadd_disjoint/general`, `overlap_deficit_bound`, `rho_absorption_collapse`, `absorption_collapse_unique_core`, `singleton_factorization` | [Mathproofs/ESAbsorptionOrder.lean](Mathproofs/ESAbsorptionOrder.lean) | [PROVED] | none | [ES-005](CONTENTS.md#es-005) |
| `s2a'_forced`, `s2b_pc`, `s2c_void`, `s2d_split`, `spectrum_partition`, `psi_union_max` | [Mathproofs/ESForcingSpectrum.lean](Mathproofs/ESForcingSpectrum.lean) | [PROVED] | none | [ES-005](CONTENTS.md#es-005) |
| `theoremA_crt`, `theoremB_scaling`, `theoremC_filter`, `theoremD_card` | [Mathproofs/ESForcingDecomp.lean](Mathproofs/ESForcingDecomp.lean) | [PROVED] | none | [ES-005](CONTENTS.md#es-005) |

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
- `DonorKernel.lean`, `ESRefinedSieveInverse.lean`, `ESUBBranchIsolation.lean`
  (verification status ambiguous or in flight — excluded pending confirmation)
