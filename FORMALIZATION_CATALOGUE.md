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
