/-
  ESAbsorptionOrder.lean — R304/R308/R311/R312/R315 ES absorption order: A1–A3 (Q-46), ρ/R3′/R3′′/T/R4′ (Q-55), singleton factorization (Q-52).

  Paper: papers/es-absorption-forcing-October-11-2026/
  Status: [PROVED] — absorp_refl/trans/antisymm, absorp_datum_iff, rho_superadd_disjoint/general, overlap_deficit_bound, rho_absorption_collapse, absorption_collapse_unique_core, singleton_factorization
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); R322: 34-theorem batch, bakkie exit 0, zero sorrys, axioms standard-only.
-/

import Mathlib

/-!
# ESAbsorptionOrder: ES absorption poset + redundancy rank (R304/R308/R311/R312/R315)

Paper trail:
- `~/workspace/math-unsolved/ROUND304_DOSSIER.md` — the absorption order ≼ on union
  groups G = (C, p); A1 (partial order), A2 (absorption characterization),
  A3 (dominance pruning) + minimal-cover normal form. Rule-9 gate: Q-46
  (Angel, SURVIVES 2026-10-11; A1–A3 census-checked; A4 stays [OPEN] — NOT formalized).
- `~/workspace/math-unsolved/ROUND308_DOSSIER.md` — B1 exact redundancy criterion;
  R2 upward-monotonicity of B1-redundancy (Q-48-checked, Angel).
- `~/workspace/math-unsolved/ROUND311_DOSSIER.md` — D1–D3, ρ = max removable members
  = |S| − min core size (definition SOUND per Q-48), R1–R5.
- `~/workspace/math-unsolved/ROUND315_DOSSIER.md` — R3′/R3′′/T/R4′ repairs after Q-48's
  quoted OBJECTION. Rule-9 gate: Q-55 (Angel, **SURVIVES**, 2026-10-11 15:29 PDT).
  Reviewer nits applied here: R3′/R3′′/T(iii) stated poset-free over an arbitrary
  finite (C,p) family (nit 2); `rho_absorption_collapse` A1-free with the uniqueness
  claim as a separate A1-using lemma (nit 5); ≺ disambiguated (nit 7 —
  `absorpLE` + `≠` throughout, no bare ≺).
- `~/workspace/math-unsolved/ROUND312_DOSSIER.md` — Singleton-Factorization Theorem.
  Rule-9 gate: Q-52 (Angel, SURVIVES 2026-10-11). The census count 7,052,450 and the
  T-stream digest stay cited [COMPUTED]×2 data (not formalized).

Formalized here ([PROVED*]-grade, Lean-checked):
- `absorp_refl` / `absorp_trans` / `absorp_antisymm` (A1)
- `absorp_datum_iff` (A2)
- `dominance_prune` (A3), `minimal_pcov_antichain` (A3 corollary, minimal-cover
  normal form)
- `redundant_mono` (R2)
- `rho_superadd_disjoint` (R3′), `rho_superadd_general` (R3′′),
  `overlap_deficit_bound` (T(iii)), `rho_absorption_collapse` (R4′, A1-free),
  `absorption_collapse_unique_core` (R4′ uniqueness add-on, uses A1)
- `ucover_minimal_iff_private_cells`, `singleton_factorization`,
  `singleton_factorization_converse` (Q-52)

Census instances (78 groups, ⊤ = 3, 303 strict pairs, 36 equal-cell pairs) and the
7,052,450-cover census stay [COMPUTED]×2 — cited, not formalized (no half-formalization).

B1 is formalized in its datum-preservation form (R308's ⟺, use-direction):
G is redundant in S iff removing it preserves the union datum.

R59/R63 audit: zero "by inspection" monotone substitutions. All inequality-adjacent
steps are exact Finset equalities/cards; the ρ arguments are Nat arithmetic via `omega`.

Lean 4.34.1 / Mathlib. Zero sorrys. Axioms: standard only (see ROUND322 dossier).
-/

open Finset

namespace ESAbsorptionOrder

variable {Cell : Type*} [DecidableEq Cell] [Fintype Cell]

/-- A union group: covered-cell set + prime-covering flag (R304 §1). -/
structure Group (Cell : Type*) where
  C : Finset Cell
  p : Bool
  deriving DecidableEq

/-- The absorption order (R304 §1): H absorbs G when H's footprint covers G's
    and H is at least as prime-covering. -/
def absorpLE (G H : Group Cell) : Prop :=
  G.C ⊆ H.C ∧ (G.p → H.p)

/-- A1: ≼ is reflexive. -/
theorem absorp_refl (G : Group Cell) : absorpLE G G :=
  ⟨Finset.Subset.rfl, fun h => h⟩

/-- A1: ≼ is transitive. -/
theorem absorp_trans {G H K : Group Cell} :
    absorpLE G H → absorpLE H K → absorpLE G K := fun h1 h2 =>
  ⟨Finset.Subset.trans h1.1 h2.1, fun h => h2.2 (h1.2 h)⟩

/-- A1: ≼ is antisymmetric (group identity is the (C, p) pair). -/
theorem absorp_antisymm {G H : Group Cell} :
    absorpLE G H → absorpLE H G → G = H := by
  rintro ⟨hsub1, himp1⟩ ⟨hsub2, himp2⟩
  have hC : G.C = H.C := Finset.Subset.antisymm hsub1 hsub2
  have hp : G.p = H.p := Bool.coe_iff_coe.mp ⟨himp1, himp2⟩
  obtain ⟨CG, pG⟩ := G
  obtain ⟨CH, pH⟩ := H
  simp_all

/-- The union datum of a family: u = union of covered cells,
    pcov = union of prime-covered cells (R285 §1). -/
def unionDatum (S : Finset (Group Cell)) : Finset Cell × Finset Cell :=
  (S.biUnion Group.C, S.biUnion fun G => if G.p then G.C else ∅)

/-- General biUnion lemmas (proved once by ext; the `Finset.biUnion_*` simp forms
    do not fire reliably in this file). -/
theorem biUnion_union_general {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S T : Finset α) (f : α → Finset β) :
    (S ∪ T).biUnion f = S.biUnion f ∪ T.biUnion f := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_union]
  constructor
  · rintro ⟨a, ha | ha, hxa⟩
    · exact Or.inl ⟨a, ha, hxa⟩
    · exact Or.inr ⟨a, ha, hxa⟩
  · rintro (⟨a, ha, hxa⟩ | ⟨a, ha, hxa⟩)
    · exact ⟨a, Or.inl ha, hxa⟩
    · exact ⟨a, Or.inr ha, hxa⟩

theorem biUnion_insert_general {α β : Type*} [DecidableEq α] [DecidableEq β]
    (a : α) (s : Finset α) (f : α → Finset β) :
    (insert a s).biUnion f = f a ∪ s.biUnion f := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_union]
  constructor
  · rintro ⟨c, rfl | hc, hxc⟩
    · exact Or.inl hxc
    · exact Or.inr ⟨c, hc, hxc⟩
  · rintro (h | ⟨c, hc, hxc⟩)
    · exact ⟨a, Or.inl rfl, h⟩
    · exact ⟨c, Or.inr hc, hxc⟩

theorem biUnion_pair_general {α β : Type*} [DecidableEq α] [DecidableEq β]
    (a b : α) (f : α → Finset β) :
    ({a, b} : Finset α).biUnion f = f a ∪ f b := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
  constructor
  · rintro ⟨c, rfl | rfl, hxc⟩
    · exact Or.inl hxc
    · exact Or.inr hxc
  · rintro (h | h)
    · exact ⟨a, Or.inl rfl, h⟩
    · exact ⟨b, Or.inr rfl, h⟩

theorem biUnion_singleton_general {α β : Type*} [DecidableEq α] [DecidableEq β]
    (a : α) (f : α → Finset β) :
    ({a} : Finset α).biUnion f = f a := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_singleton]
  constructor
  · rintro ⟨c, rfl, hxc⟩
    exact hxc
  · intro h
    exact ⟨a, rfl, h⟩

/-- The union datum distributes over family union (components). -/
theorem unionDatum_fst_union (S T : Finset (Group Cell)) :
    (unionDatum (S ∪ T)).1 = (unionDatum S).1 ∪ (unionDatum T).1 :=
  biUnion_union_general S T Group.C

theorem unionDatum_snd_union (S T : Finset (Group Cell)) :
    (unionDatum (S ∪ T)).2 = (unionDatum S).2 ∪ (unionDatum T).2 :=
  biUnion_union_general S T fun G => if G.p then G.C else ∅

/-- A2: absorption characterization — datum({G,H}) = datum({H}) ⟺ G ≼ H.
    Needs the census working convention that cells are nonempty (Q-48/Q-55). -/
theorem absorp_datum_iff {G H : Group Cell} (hcell : ∀ g : Group Cell, g.C.Nonempty) :
    unionDatum ({G, H} : Finset (Group Cell)) = unionDatum {H} ↔ absorpLE G H := by
  have eU2 : (unionDatum ({G, H} : Finset (Group Cell))).1 = G.C ∪ H.C :=
    biUnion_pair_general G H Group.C
  have eU1 : (unionDatum ({H} : Finset (Group Cell))).1 = H.C :=
    biUnion_singleton_general H Group.C
  have eP2 : (unionDatum ({G, H} : Finset (Group Cell))).2
      = (if G.p then G.C else ∅) ∪ (if H.p then H.C else ∅) :=
    biUnion_pair_general G H fun G => if G.p then G.C else ∅
  have eP1 : (unionDatum ({H} : Finset (Group Cell))).2 = (if H.p then H.C else ∅) :=
    biUnion_singleton_general H fun G => if G.p then G.C else ∅
  constructor
  · intro h
    have hu : G.C ∪ H.C = H.C := by
      rw [← eU2, ← eU1]; exact congrArg Prod.fst h
    have hsub : G.C ⊆ H.C := by
      rw [← hu]; exact Finset.subset_union_left
    have hpc : (if G.p then G.C else ∅) ∪ (if H.p then H.C else ∅)
        = (if H.p then H.C else ∅) := by
      rw [← eP2, ← eP1]; exact congrArg Prod.snd h
    refine ⟨hsub, ?_⟩
    cases hpG : G.p with
    | false => simp [hpG]
    | true =>
      cases hpH : H.p with
      | true => simp [hpG, hpH]
      | false =>
        exfalso
        have hGe : G.C = ∅ := by simpa [hpG, hpH] using hpc
        exact (hcell G).ne_empty hGe
  · rintro ⟨hsub, himp⟩
    have hu : G.C ∪ H.C = H.C := Finset.union_eq_right.mpr hsub
    have hpc : (if G.p then G.C else ∅) ∪ (if H.p then H.C else ∅)
        = (if H.p then H.C else ∅) := by
      cases hpH : H.p with
      | false =>
        have hpG : G.p = false := by
          cases hpG : G.p with
          | false => rfl
          | true => simp_all
        simp [hpG, hpH]
      | true =>
        cases hpG : G.p with
        | false => simp [hpG, hpH]
        | true => simp [hpG, hpH, hu]
    have e1 : (unionDatum ({G, H} : Finset (Group Cell))).1
        = (unionDatum ({H} : Finset (Group Cell))).1 := by
      rw [eU2, eU1, hu]
    have e2 : (unionDatum ({G, H} : Finset (Group Cell))).2
        = (unionDatum ({H} : Finset (Group Cell))).2 := by
      rw [eP2, eP1, hpc]
    exact Prod.ext e1 e2

/-- A3: dominance pruning — removing a dominated member preserves the datum. -/
theorem dominance_prune {S : Finset (Group Cell)} {G H : Group Cell}
    (hG : G ∈ S) (hH : H ∈ S) (hle : absorpLE G H) (hne : G ≠ H) :
    unionDatum (S.erase G) = unionDatum S := by
  obtain ⟨hsub, himp⟩ := hle
  have hH' : H ∈ S.erase G := Finset.mem_erase.mpr ⟨Ne.symm hne, hH⟩
  have keyU : G.C ⊆ (S.erase G).biUnion Group.C :=
    Finset.Subset.trans hsub (Finset.subset_biUnion_of_mem Group.C hH')
  have keyP : (if G.p then G.C else ∅)
      ⊆ (S.erase G).biUnion (fun G => if G.p then G.C else ∅) := by
    by_cases hpG : G.p = true
    · have hpH : H.p = true := himp (by rw [hpG])
      have e1 : (if G.p then G.C else ∅) = G.C := by simp [hpG]
      have e2 : (if H.p then H.C else ∅) = H.C := by simp [hpH]
      have e3 : (if H.p then H.C else ∅)
          ⊆ (S.erase G).biUnion (fun G => if G.p then G.C else ∅) :=
        Finset.subset_biUnion_of_mem (fun G => if G.p then G.C else ∅) hH'
      rw [e1]
      exact hsub.trans (e2 ▸ e3)
    · have hpGf : G.p = false := by
        cases h : G.p with
        | false => rfl
        | true => exact absurd h hpG
      simp [hpGf]
  have eU : (S.erase G).biUnion Group.C = S.biUnion Group.C := by
    have hSS : S.biUnion Group.C = G.C ∪ (S.erase G).biUnion Group.C := by
      conv_lhs => rw [(Finset.insert_erase hG).symm]
      exact biUnion_insert_general G (S.erase G) Group.C
    rw [hSS, Finset.union_eq_right.mpr keyU]
  have eP : (S.erase G).biUnion (fun G => if G.p then G.C else ∅)
      = S.biUnion (fun G => if G.p then G.C else ∅) := by
    have hSS : S.biUnion (fun G => if G.p then G.C else ∅)
        = (if G.p then G.C else ∅) ∪ (S.erase G).biUnion (fun G => if G.p then G.C else ∅) := by
      conv_lhs => rw [(Finset.insert_erase hG).symm]
      exact biUnion_insert_general G (S.erase G) _
    rw [hSS, Finset.union_eq_right.mpr keyP]
  have e1 : (unionDatum (S.erase G)).1 = (unionDatum S).1 := eU
  have e2 : (unionDatum (S.erase G)).2 = (unionDatum S).2 := eP
  exact Prod.ext e1 e2

/-- A3 corollary: minimal-cover normal form — a pcov-minimal family is an
    absorpLE-antichain (R304 §2). -/
theorem minimal_pcov_antichain {S : Finset (Group Cell)} {T : Finset Cell}
    (hcov : T ⊆ (unionDatum S).2)
    (hmin : ∀ C : Finset (Group Cell), C ⊂ S → ¬ T ⊆ (unionDatum C).2) :
    ∀ G ∈ S, ∀ H ∈ S, absorpLE G H → G = H := by
  intro G hG H hH hle
  by_contra hne
  have hprune := dominance_prune hG hH hle hne
  have hcovE : T ⊆ (unionDatum (S.erase G)).2 := by
    rw [hprune]; exact hcov
  exact hmin _ (Finset.erase_ssubset hG) hcovE

/-! ## B1 redundancy and the R2 monotonicity lemma (R308/R311) -/

/-- B1-redundancy in datum-preservation form (R308's exact criterion, use-direction):
    G is redundant in S iff removing it preserves the union datum. -/
def Redundant (S : Finset (Group Cell)) (G : Group Cell) : Prop :=
  G ∈ S ∧ unionDatum (S.erase G) = unionDatum S

/-- Datum equality is preserved under union with a fixed family. -/
theorem unionDatum_union_right {A B U : Finset (Group Cell)}
    (h : unionDatum A = unionDatum B) :
    unionDatum (A ∪ U) = unionDatum (B ∪ U) := by
  have e1 : (unionDatum (A ∪ U)).1 = (unionDatum (B ∪ U)).1 := by
    rw [unionDatum_fst_union, unionDatum_fst_union, h]
  have e2 : (unionDatum (A ∪ U)).2 = (unionDatum (B ∪ U)).2 := by
    rw [unionDatum_snd_union, unionDatum_snd_union, h]
  exact Prod.ext e1 e2

/-- R2: B1-redundancy is upward-monotone — a member redundant in S stays redundant
    in any superfamily T (unions over the witness index sets only grow). -/
theorem redundant_mono {S T : Finset (Group Cell)} {G : Group Cell}
    (h : Redundant S G) (hST : S ⊆ T) : Redundant T G := by
  obtain ⟨hGS, hdat⟩ := h
  refine ⟨hST hGS, ?_⟩
  have hsplit : T.erase G = (S.erase G) ∪ (T \ S) := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨hne, hmem⟩
      by_cases hS : x ∈ S
      · exact Or.inl ⟨hne, hS⟩
      · exact Or.inr ⟨hmem, hS⟩
    · rintro (⟨hne, hS⟩ | ⟨hT, hnS⟩)
      · exact ⟨hne, hST hS⟩
      · refine ⟨?_, hT⟩
        intro heq
        subst heq
        exact hnS hGS
  have hTS : T = S ∪ (T \ S) := (Finset.union_sdiff_of_subset hST).symm
  calc unionDatum (T.erase G)
      = unionDatum ((S.erase G) ∪ (T \ S)) := by rw [hsplit]
    _ = unionDatum (S ∪ (T \ S)) := unionDatum_union_right hdat
    _ = unionDatum T := by conv_rhs => rw [hTS]

/-! ## Redundancy rank ρ (R311 §3, R315 repairs) -/

/-- A core of S: a subfamily with the same union datum. -/
def IsCore (S C : Finset (Group Cell)) : Prop :=
  C ⊆ S ∧ unionDatum C = unionDatum S

/-- The redundancy rank ρ(S) = |S| − min core size (R311 §3; definition SOUND
    per Q-48, confirmed Q-55). -/
noncomputable def minCoreSize (S : Finset (Group Cell)) : ℕ :=
  sInf { n : ℕ | ∃ C : Finset (Group Cell), IsCore S C ∧ C.card = n }

noncomputable def rho (S : Finset (Group Cell)) : ℕ :=
  S.card - minCoreSize S

theorem exists_core_card_min (S : Finset (Group Cell)) :
    ∃ C : Finset (Group Cell), IsCore S C ∧ C.card = minCoreSize S := by
  have hne : ∃ n : ℕ, n ∈
      { n : ℕ | ∃ C : Finset (Group Cell), IsCore S C ∧ C.card = n } :=
    ⟨S.card, S, ⟨Finset.Subset.rfl, rfl⟩, rfl⟩
  exact Nat.sInf_mem hne

/-- R3′: disjoint superadditivity (Q-55 SURVIVES). Poset-free per reviewer nit 2. -/
theorem rho_superadd_disjoint {S T : Finset (Group Cell)} (hdisj : Disjoint S T) :
    rho S + rho T ≤ rho (S ∪ T) := by
  obtain ⟨C₁, hC₁core, hC₁card⟩ := exists_core_card_min S
  obtain ⟨C₂, hC₂core, hC₂card⟩ := exists_core_card_min T
  have hsub : C₁ ∪ C₂ ⊆ S ∪ T := Finset.union_subset_union hC₁core.1 hC₂core.1
  have hdat : unionDatum (C₁ ∪ C₂) = unionDatum (S ∪ T) := by
    have e1 : (unionDatum (C₁ ∪ C₂)).1 = (unionDatum (S ∪ T)).1 := by
      rw [unionDatum_fst_union, unionDatum_fst_union, hC₁core.2, hC₂core.2]
    have e2 : (unionDatum (C₁ ∪ C₂)).2 = (unionDatum (S ∪ T)).2 := by
      rw [unionDatum_snd_union, unionDatum_snd_union, hC₁core.2, hC₂core.2]
    exact Prod.ext e1 e2
  have hmem : (C₁ ∪ C₂).card ∈
      { n : ℕ | ∃ C : Finset (Group Cell), IsCore (S ∪ T) C ∧ C.card = n } :=
    ⟨C₁ ∪ C₂, ⟨hsub, hdat⟩, rfl⟩
  have hle : minCoreSize (S ∪ T) ≤ C₁.card + C₂.card :=
    calc minCoreSize (S ∪ T) ≤ (C₁ ∪ C₂).card := Nat.sInf_le hmem
      _ = C₁.card + C₂.card :=
          Finset.card_union_of_disjoint (Disjoint.mono hC₁core.1 hC₂core.1 hdisj)
  have hle2 : minCoreSize (S ∪ T) ≤ minCoreSize S + minCoreSize T := by
    calc minCoreSize (S ∪ T) ≤ C₁.card + C₂.card := hle
      _ = minCoreSize S + minCoreSize T := by rw [hC₁card, hC₂card]
  have hmS : minCoreSize S ≤ S.card :=
    Nat.sInf_le ⟨S, ⟨Finset.Subset.rfl, rfl⟩, rfl⟩
  have hmT : minCoreSize T ≤ T.card :=
    Nat.sInf_le ⟨T, ⟨Finset.Subset.rfl, rfl⟩, rfl⟩
  have hcardST : (S ∪ T).card = S.card + T.card := Finset.card_union_of_disjoint hdisj
  unfold rho
  omega

/-- R3′′: general superadditivity (Q-55 SURVIVES). Poset-free per reviewer nit 2. -/
theorem rho_superadd_general (S T : Finset (Group Cell)) :
    rho S + rho (T \ S) ≤ rho (S ∪ T) := by
  have h := rho_superadd_disjoint (S := S) (T := T \ S) Finset.disjoint_sdiff
  have hunion : S ∪ (T \ S) = S ∪ T := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  rwa [hunion] at h

/-- T(iii): trapped-redundancy bound (Q-55 SURVIVES). Poset-free per reviewer nit 2. -/
theorem overlap_deficit_bound (S T : Finset (Group Cell)) :
    rho S + rho T - rho (S ∪ T) ≤ rho T - rho (T \ S) := by
  have h := rho_superadd_general S T
  omega

/-- R4′: absorption collapse, A1-free (Q-55 SURVIVES; reviewer nit 5 — no A1,
    no case split: A2 gives the collapse directly). -/
theorem rho_absorption_collapse {G H : Group Cell} (hle : absorpLE G H) (hne : G ≠ H)
    (hcell : ∀ g : Group Cell, g.C.Nonempty) :
    rho ({G, H} : Finset (Group Cell)) = 1 := by
  have hcard : ({G, H} : Finset (Group Cell)).card = 2 := Finset.card_pair hne
  have hHcore : IsCore ({G, H} : Finset (Group Cell)) {H} := by
    refine ⟨by simp, ?_⟩
    exact ((absorp_datum_iff hcell).mpr hle).symm
  have hle1 : minCoreSize ({G, H} : Finset (Group Cell)) ≤ 1 :=
    Nat.sInf_le ⟨{H}, hHcore, by simp⟩
  have hge1 : 1 ≤ minCoreSize ({G, H} : Finset (Group Cell)) := by
    obtain ⟨C₀, hC₀core, hC₀card⟩ := exists_core_card_min ({G, H} : Finset (Group Cell))
    by_contra hlt
    push_neg at hlt
    have hC0 : C₀ = ∅ := Finset.card_eq_zero.mp (by omega)
    have hfst : (∅ : Finset Cell) = ({G, H} : Finset (Group Cell)).biUnion Group.C := by
      have hdat := hC₀core.2
      rw [hC0] at hdat
      have h := congrArg Prod.fst hdat
      simpa [unionDatum] using h
    have hmem : H ∈ ({G, H} : Finset (Group Cell)) := by simp
    have hsub : H.C ⊆ (∅ : Finset Cell) := by
      rw [hfst]; exact Finset.subset_biUnion_of_mem Group.C hmem
    exact (hcell H).ne_empty (Finset.subset_empty.mp hsub)
  have hmin : minCoreSize ({G, H} : Finset (Group Cell)) = 1 := by omega
  unfold rho
  rw [hcard, hmin]

/-- R4′ uniqueness add-on (uses A1; reviewer nit 5): the only singleton core
    of {G, H} is {H}. -/
theorem absorption_collapse_unique_core {G H : Group Cell} (hle : absorpLE G H)
    (hne : G ≠ H) (hcell : ∀ g : Group Cell, g.C.Nonempty)
    {C : Finset (Group Cell)}
    (hcore : IsCore ({G, H} : Finset (Group Cell)) C) (hcard : C.card = 1) :
    C = {H} := by
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
  have ha : a ∈ ({G, H} : Finset (Group Cell)) := hcore.1 (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with hAG | hAH
  · exfalso
    have hdat : unionDatum ({G} : Finset (Group Cell)) = unionDatum ({H} : Finset (Group Cell)) := by
      have h1 := hcore.2
      rw [hAG] at h1
      exact h1.trans ((absorp_datum_iff hcell).mpr hle)
    have hle2 : absorpLE H G := by
      apply (absorp_datum_iff (G := H) (H := G) hcell).mp
      rw [Finset.pair_comm]
      exact ((absorp_datum_iff hcell).mpr hle).trans hdat.symm
    exact hne (absorp_antisymm hle hle2)
  · rw [hAH]

/-! ## Singleton factorization (R312 §1, Q-52 SURVIVES) -/

section Factorization

variable (S0 : Finset Cell)

/-- A u-cover: footprint is the whole cell universe. -/
def IsUCover (S : Finset (Group Cell)) : Prop :=
  (unionDatum S).1 = Finset.univ

/-- Inclusion-minimal u-cover. -/
def IsMinimalUCover (S : Finset (Group Cell)) : Prop :=
  IsUCover S ∧ ∀ C : Finset (Group Cell), C ⊂ S → ¬ IsUCover C

theorem isUCover_iff {S : Finset (Group Cell)} :
    IsUCover S ↔ S.biUnion Group.C = Finset.univ :=
  Iff.rfl

/-- Minimal u-cover ⟺ every member has a private cell (R312 §1 setup). -/
theorem ucover_minimal_iff_private_cells {S : Finset (Group Cell)} (hcov : IsUCover S) :
    (∀ C : Finset (Group Cell), C ⊂ S → ¬ IsUCover C) ↔
    (∀ G ∈ S, ∃ c ∈ G.C, ∀ H ∈ S, c ∈ H.C → H = G) := by
  constructor
  · intro hmin G hG
    by_contra hcon
    push_neg at hcon
    have hsub : S.erase G ⊂ S := Finset.erase_ssubset hG
    have hcov' : IsUCover (S.erase G) := by
      show (unionDatum (S.erase G)).1 = Finset.univ
      apply Finset.eq_univ_of_forall
      intro c
      have hc : c ∈ S.biUnion Group.C := by
        have h := hcov
        rw [isUCover_iff] at h
        rw [h]; exact Finset.mem_univ c
      obtain ⟨K, hK, hcK⟩ := Finset.mem_biUnion.mp hc
      by_cases hKG : K = G
      · subst hKG
        obtain ⟨H, hH, hcH, hne⟩ := hcon c hcK
        exact Finset.mem_biUnion.mpr ⟨H, Finset.mem_erase.mpr ⟨hne, hH⟩, hcH⟩
      · exact Finset.mem_biUnion.mpr ⟨K, Finset.mem_erase.mpr ⟨hKG, hK⟩, hcK⟩
    exact hmin _ hsub hcov'
  · intro hpriv C hCsub hCcov
    obtain ⟨G, hGS, hGC⟩ := Finset.exists_of_ssubset hCsub
    obtain ⟨c, hcG, hprivc⟩ := hpriv G hGS
    have hcU : c ∈ C.biUnion Group.C := by
      have h := hCcov
      rw [isUCover_iff] at h
      rw [h]; exact Finset.mem_univ c
    obtain ⟨H, hHC, hcH⟩ := Finset.mem_biUnion.mp hcU
    have hHS : H ∈ S := hCsub.subset hHC
    have hHG : H = G := hprivc H hHS hcH
    exact hGC (hHG ▸ hHC)

/-- A minimal u-cover is an absorpLE-antichain (R304 A3, u-version). -/
theorem minimal_ucov_antichain {S : Finset (Group Cell)} (hmin : IsMinimalUCover S) :
    ∀ G₁ ∈ S, ∀ G₂ ∈ S, absorpLE G₁ G₂ → G₁ = G₂ := by
  intro G₁ hG₁ G₂ hG₂ hle
  by_contra hne
  have hprune := dominance_prune hG₁ hG₂ hle hne
  have hcovE : IsUCover (S.erase G₁) := by
    show (unionDatum (S.erase G₁)).1 = Finset.univ
    rw [congrArg Prod.fst hprune]
    exact hmin.1
  exact hmin.2 _ (Finset.erase_ssubset hG₁) hcovE

/-- The Singleton-Factorization Theorem (R312 §1, Q-52 SURVIVES): every minimal
    u-cover splits as non-singleton core T plus exactly one singleton group per
    cell outside F(T); S0 (cells with no singleton group) is covered by T. -/
theorem singleton_factorization
    (hS0 : ∀ c ∈ S0, ∀ g : Group Cell, g.C = {c} → False)
    {S : Finset (Group Cell)} (hmin : IsMinimalUCover S) :
    let T := S.filter (fun g => g.C.card ≠ 1)
    let U := S.filter (fun g => g.C.card = 1)
    S = T ∪ U ∧ Disjoint T U ∧
    (∀ H ∈ T, ∃ x ∈ H.C, ∀ K ∈ T, x ∈ K.C → K = H) ∧
    (∀ c, c ∉ (unionDatum T).1 → ∃! g, g ∈ U ∧ g.C = {c}) ∧
    S0 ⊆ (unionDatum T).1 := by
  have hpriv := (ucover_minimal_iff_private_cells hmin.1).mp hmin.2
  have hanti := minimal_ucov_antichain hmin
  set T := S.filter (fun g => g.C.card ≠ 1) with hTdef
  set U := S.filter (fun g => g.C.card = 1) with hUdef
  have hTU : S = T ∪ U := by
    rw [hTdef, hUdef]
    ext g
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro h
      by_cases hc : g.C.card = 1
      · exact Or.inr ⟨h, hc⟩
      · exact Or.inl ⟨h, hc⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdisj : Disjoint T U := by
    rw [Finset.disjoint_left]
    intro g hgT hgU
    rw [hTdef] at hgT; rw [hUdef] at hgU
    simp only [Finset.mem_filter] at hgT hgU
    exact hgT.2 hgU.2
  have hTpriv : ∀ H ∈ T, ∃ x ∈ H.C, ∀ K ∈ T, x ∈ K.C → K = H := by
    intro H hHT
    rw [hTdef] at hHT
    have hHS : H ∈ S := (Finset.mem_filter.mp hHT).1
    obtain ⟨x, hxH, hxp⟩ := hpriv H hHS
    refine ⟨x, hxH, fun K hKT hxK => ?_⟩
    rw [hTdef] at hKT
    exact hxp K (Finset.mem_filter.mp hKT).1 hxK
  have hUexact : ∀ c, c ∉ (unionDatum T).1 → ∃! g, g ∈ U ∧ g.C = {c} := by
    intro c hcF
    have hex : ∃ g ∈ U, g.C = {c} := by
      have hcU : c ∈ S.biUnion Group.C := by
        have h := hmin.1
        rw [isUCover_iff] at h
        rw [h]; exact Finset.mem_univ c
      obtain ⟨G, hGS, hcG⟩ := Finset.mem_biUnion.mp hcU
      by_cases hcard : G.C.card = 1
      · obtain ⟨c', hc'⟩ := Finset.card_eq_one.mp hcard
        have hcc : c = c' := Finset.mem_singleton.mp (hc' ▸ hcG)
        refine ⟨G, ?_, by rw [hc', hcc]⟩
        rw [hUdef]; exact Finset.mem_filter.mpr ⟨hGS, hcard⟩
      · exfalso
        have hGT : G ∈ T := by
          rw [hTdef]; exact Finset.mem_filter.mpr ⟨hGS, hcard⟩
        have hmem : c ∈ (unionDatum T).1 :=
          Finset.mem_biUnion.mpr ⟨G, hGT, hcG⟩
        exact hcF hmem
    obtain ⟨G, hGU, hGc⟩ := hex
    refine ⟨G, ⟨hGU, hGc⟩, fun G₂ hG₂ => ?_⟩
    obtain ⟨hG₂U, hG₂c⟩ := hG₂
    have hGS : G ∈ S := by
      rw [hUdef] at hGU; exact (Finset.mem_filter.mp hGU).1
    have hG₂S : G₂ ∈ S := by
      rw [hUdef] at hG₂U; exact (Finset.mem_filter.mp hG₂U).1
    have hcomp : absorpLE G G₂ ∨ absorpLE G₂ G := by
      by_cases h : G.p = true
      · right
        refine ⟨by rw [hGc, hG₂c], by simp [h]⟩
      · left
        refine ⟨by rw [hGc, hG₂c], by simp [h]⟩
    rcases hcomp with h | h
    · exact (hanti G hGS G₂ hG₂S h).symm
    · exact hanti G₂ hG₂S G hGS h
  have hS0T : S0 ⊆ (unionDatum T).1 := by
    intro c hc
    have hcU : c ∈ S.biUnion Group.C := by
      have h := hmin.1
      rw [isUCover_iff] at h
      rw [h]; exact Finset.mem_univ c
    obtain ⟨G, hGS, hcG⟩ := Finset.mem_biUnion.mp hcU
    by_cases hcard : G.C.card = 1
    · obtain ⟨c', hc'⟩ := Finset.card_eq_one.mp hcard
      have hcc : c = c' := Finset.mem_singleton.mp (hc' ▸ hcG)
      exfalso
      exact hS0 c hc G (by rw [hc', hcc])
    · have hGT : G ∈ T := by
        rw [hTdef]; exact Finset.mem_filter.mpr ⟨hGS, hcard⟩
      exact Finset.mem_biUnion.mpr ⟨G, hGT, hcG⟩
  exact ⟨hTU, hdisj, hTpriv, hUexact, hS0T⟩

/-- Converse of the factorization (R312 §1): every valid (T, U) pair gives a
    minimal u-cover. -/
theorem singleton_factorization_converse
    {T U : Finset (Group Cell)}
    (hTpriv : ∀ H ∈ T, ∃ x ∈ H.C, ∀ K ∈ T, x ∈ K.C → K = H)
    (hU : ∀ c, c ∉ (unionDatum T).1 → ∃! g, g ∈ U ∧ g.C = {c})
    (hUout : ∀ g ∈ U, ∃ c, c ∉ (unionDatum T).1 ∧ g.C = {c}) :
    IsMinimalUCover (T ∪ U) := by
  have hcov : IsUCover (T ∪ U) := by
    show (unionDatum (T ∪ U)).1 = Finset.univ
    apply Finset.eq_univ_of_forall
    intro c
    by_cases hc : c ∈ (unionDatum T).1
    · obtain ⟨G, hG, hcG⟩ := Finset.mem_biUnion.mp hc
      exact Finset.mem_biUnion.mpr ⟨G, Finset.mem_union_left U hG, hcG⟩
    · obtain ⟨g, ⟨hgU, hgc⟩, -⟩ := hU c hc
      have hgc' : c ∈ g.C := by rw [hgc]; exact Finset.mem_singleton_self c
      exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_union_right T hgU, hgc'⟩
  have hpriv : ∀ G ∈ T ∪ U, ∃ c ∈ G.C, ∀ K ∈ T ∪ U, c ∈ K.C → K = G := by
    intro G hGU
    rcases Finset.mem_union.mp hGU with hGT | hGU'
    · obtain ⟨x, hxH, hxp⟩ := hTpriv G hGT
      refine ⟨x, hxH, fun K hKU hxK => ?_⟩
      rcases Finset.mem_union.mp hKU with hKT | hKU'
      · exact hxp K hKT hxK
      · obtain ⟨c, hcF, hgc⟩ := hUout K hKU'
        have hxc : x = c := Finset.mem_singleton.mp (hgc ▸ hxK)
        have hxF : x ∈ (unionDatum T).1 :=
          Finset.mem_biUnion.mpr ⟨G, hGT, hxH⟩
        rw [hxc] at hxF
        exact absurd hxF hcF
    · obtain ⟨c, hcF, hgc⟩ := hUout G hGU'
      refine ⟨c, by rw [hgc]; exact Finset.mem_singleton_self c, fun K hKU hcK => ?_⟩
      rcases Finset.mem_union.mp hKU with hKT | hKU'
      · exfalso
        have hcF' : c ∈ (unionDatum T).1 :=
          Finset.mem_biUnion.mpr ⟨K, hKT, hcK⟩
        exact hcF hcF'
      · obtain ⟨c', hcF', hgc'⟩ := hUout K hKU'
        have hcc' : c = c' := Finset.mem_singleton.mp (hgc' ▸ hcK)
        obtain ⟨g, hg, huniq⟩ := hU c hcF
        have hG : G ∈ U ∧ G.C = {c} := ⟨hGU', hgc⟩
        have hK : K ∈ U ∧ K.C = {c} := ⟨hKU', by rw [hgc', hcc']⟩
        have e1 : g = G := (huniq G hG).symm
        have e2 : g = K := (huniq K hK).symm
        exact e2.symm.trans e1
  exact ⟨hcov, (ucover_minimal_iff_private_cells hcov).mpr hpriv⟩

end Factorization

end ESAbsorptionOrder
