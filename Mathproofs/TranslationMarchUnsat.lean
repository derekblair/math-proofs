/-
  TranslationMarchUnsat.lean — Corrected R233 unsaturated translation march: rigid interior-hole conveyor, edge terms, propagation, rescue thresholds, additive bound |holes(A)|+|t|.

  Paper: papers/translation-march-dip-October-11-2026/
  Status: [PROVED] — march_unsat_pos/neg, propagation_subset, rescue_threshold_pos/neg, additive_bound_pos/neg
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); R250: exit 0 both sides, zero sorrys, axioms standard-only.
-/

/-
R233 — Unsaturated Translation March theorem (ROUND233_DOSSIER.md).

Generalises Mathproofs.TranslationMarch (R227, saturated case): for ANY Sidon
A ⊆ [1,N] (no saturation assumed) with A+t ⊆ [1,N], the holes of A+t split
into a rigidly-propagated term (A's own holes shifted by t, clipped to
[1,N]) plus the saturated-march edge term. Saturation recovery: holes(A)=∅
kills the propagation term and the statement reduces to R227's Theorem 1.

FORMALISATION NOTE (statement correction vs the hand proof): the dossier's
proof writes S₂ = [1,t] (t≥0) without a nonemptiness hypothesis, but for
A = ∅ and t > N the stated identity is FALSE as written
(counterexample: N=184, A=∅, t=200 gives holes(A+t)=[1,184] but the
right-hand side is [1,200]). With A nonempty, A+t ⊆ [1,N] forces t ≤ N−1
(t ≤ 0: t ≥ 1−N), so the clip is vacuous and the dossier's unclipped edge
term is exact. Every decomposition theorem below therefore carries an
explicit `A.Nonempty` hypothesis — the one-line fix the hand proof needs.
All intended instances (9-element seeds) satisfy it. The propagation,
rescue-threshold and additive-bound corollaries are proved from the
corrected decomposition.

Claims formalised (machine-checked):
- `holes_filter`: holes(A+t) = {p ∈ [1,N] : p−t ∉ W(A)} (from rigidity).
- `march_unsat_pos` / `march_unsat_neg`: the decomposition identity
  (Theorem), t≥0 / t≤0.
- `march_unsat_disjoint_pos` / `march_unsat_disjoint_neg`: the union is disjoint.
- `propagation_subset`: the propagation term is always ⊆ holes(A+t)
  (Corollary: Propagation).
- `rescue_threshold_pos` / `rescue_threshold_neg`: the propagation term
  vanishes exactly past t > N − min(holes(A)) (Corollary: Rescue threshold).
- `additive_bound_pos` / `additive_bound_neg`: |holes(A+t)| ≤ |holes(A)| + |t|
  (Corollary: Additive bound). The saturated bound |holes| ≤ |t| is NOT
  claimed (it fails: A0 at t=1 has 4 holes — see dossier).
The [COMPUTED] march tables (450/450, six seeds) are cited from
ROUND233_DOSSIER.md, not formalised.

Status: imports the [PROVED] TranslationMarch module (R227 Lemma 1,
machine-checked) for the shared W(A)/B(A)/holes definitions and rigidity.
Requires hostile review clearance per PROGRAM.md rule 9 before [PROVED].

Checked: Lean 4.34.1 + Mathlib v4.34.1, `lake build`, zero sorrys,
`#print axioms` standard-only.
-/
import Mathproofs.TranslationMarch

namespace TranslationMarchUnsat

open Finset

/-- Holes of a translate, unclipped shadow form: from rigidity,
    holes(A+t) = {p ∈ [1,N] : p−t ∉ W(A)}. -/
theorem holes_filter (A : Finset ℤ) (N t : ℤ) :
    TranslationMarch.holes (A.image (· + t)) N
      = (Finset.Icc 1 N).filter (fun p => p - t ∉ TranslationMarch.rawBlocked A) := by
  ext p
  simp only [TranslationMarch.holes, TranslationMarch.blocked,
    TranslationMarch.rawBlocked_translate, TranslationMarch.mem_image_add,
    Finset.mem_sdiff, Finset.mem_inter, Finset.mem_filter]
  tauto

/-- Translation by t is injective. -/
theorem injective_add_right (t : ℤ) : Function.Injective (· + t : ℤ → ℤ) := by
  intro a b h
  have h' : a + t = b + t := h
  omega

/-- Valid shifts of a nonempty A ⊆ [1,N] lie in [1−N, N−1]. -/
theorem valid_shift_mem_Icc (A : Finset ℤ) (N t : ℤ)
    (hne : A.Nonempty) (hA : A ⊆ Finset.Icc 1 N)
    (hAt : A.image (· + t) ⊆ Finset.Icc 1 N) :
    t ∈ Finset.Icc (1 - N) (N - 1) := by
  obtain ⟨a, ha⟩ := hne
  have haI := hA ha
  have hatI := hAt (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  rw [Finset.mem_Icc] at haI hatI ⊢
  omega

/-- Theorem (Unsaturated Translation March), t ≥ 0: holes(A+t) is the
    disjoint union of the rigidly propagated holes and the shadow-edge term. -/
theorem march_unsat_pos (A : Finset ℤ) (N t : ℤ)
    (hne : A.Nonempty) (hA : A ⊆ Finset.Icc 1 N)
    (hAt : A.image (· + t) ⊆ Finset.Icc 1 N) (ht : 0 ≤ t) :
    TranslationMarch.holes (A.image (· + t)) N
      = ((TranslationMarch.holes A N).image (· + t) ∩ Finset.Icc 1 N)
        ∪ (Finset.Icc 1 t).filter (fun p => p - t ∉ TranslationMarch.rawBlocked A) := by
  have htN : t ≤ N - 1 := by
    have hmem := valid_shift_mem_Icc A N t hne hA hAt
    rw [Finset.mem_Icc] at hmem
    omega
  have hmemW : ∀ q : ℤ, q ∈ TranslationMarch.holes A N →
      q ∉ TranslationMarch.rawBlocked A := by
    intro q hq
    simp only [TranslationMarch.holes, TranslationMarch.blocked,
      Finset.mem_sdiff, Finset.mem_inter] at hq
    exact fun hw => hq.2 ⟨hw, hq.1⟩
  have hmemI : ∀ q : ℤ, q ∈ TranslationMarch.holes A N → q ∈ Finset.Icc 1 N := by
    intro q hq
    simp only [TranslationMarch.holes, Finset.mem_sdiff] at hq
    exact hq.1
  rw [holes_filter]
  ext p
  simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_inter,
    Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hp1, hpN⟩, hW⟩
    by_cases hpt : p ≤ t
    · exact Or.inr ⟨⟨hp1, hpt⟩, hW⟩
    · push_neg at hpt
      refine Or.inl ⟨⟨p - t, ?_, by ring⟩, hp1, hpN⟩
      have h1 : 1 ≤ p - t := by omega
      have h2 : p - t ≤ N := by omega
      have hW' : p - t ∉ TranslationMarch.rawBlocked A ∩ Finset.Icc 1 N := by
        intro hcon
        rw [Finset.mem_inter] at hcon
        exact hW hcon.1
      have hmem : p - t ∈ TranslationMarch.holes A N := by
        simp only [TranslationMarch.holes, TranslationMarch.blocked,
          Finset.mem_sdiff]
        exact ⟨Finset.mem_Icc.mpr ⟨h1, h2⟩, hW'⟩
      exact hmem
  · rintro (⟨⟨q, hq, rfl⟩, hp1, hpN⟩ | ⟨⟨hp1, hpt⟩, hW⟩)
    · refine ⟨⟨hp1, hpN⟩, ?_⟩
      have hqq : q + t - t = q := by ring
      rw [hqq]
      exact hmemW q hq
    · refine ⟨⟨hp1, by omega⟩, hW⟩

/-- Theorem (Unsaturated Translation March), t ≤ 0: mirror image. -/
theorem march_unsat_neg (A : Finset ℤ) (N t : ℤ)
    (hne : A.Nonempty) (hA : A ⊆ Finset.Icc 1 N)
    (hAt : A.image (· + t) ⊆ Finset.Icc 1 N) (ht : t ≤ 0) :
    TranslationMarch.holes (A.image (· + t)) N
      = ((TranslationMarch.holes A N).image (· + t) ∩ Finset.Icc 1 N)
        ∪ (Finset.Icc (N + t + 1) N).filter
            (fun p => p - t ∉ TranslationMarch.rawBlocked A) := by
  have htN : 1 - N ≤ t := by
    have hmem := valid_shift_mem_Icc A N t hne hA hAt
    rw [Finset.mem_Icc] at hmem
    omega
  have hmemW : ∀ q : ℤ, q ∈ TranslationMarch.holes A N →
      q ∉ TranslationMarch.rawBlocked A := by
    intro q hq
    simp only [TranslationMarch.holes, TranslationMarch.blocked,
      Finset.mem_sdiff, Finset.mem_inter] at hq
    exact fun hw => hq.2 ⟨hw, hq.1⟩
  rw [holes_filter]
  ext p
  simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_inter,
    Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hp1, hpN⟩, hW⟩
    by_cases hpt : N + t + 1 ≤ p
    · exact Or.inr ⟨⟨hpt, hpN⟩, hW⟩
    · push_neg at hpt
      refine Or.inl ⟨⟨p - t, ?_, by ring⟩, hp1, hpN⟩
      have h1 : 1 ≤ p - t := by omega
      have h2 : p - t ≤ N := by omega
      have hW' : p - t ∉ TranslationMarch.rawBlocked A ∩ Finset.Icc 1 N := by
        intro hcon
        rw [Finset.mem_inter] at hcon
        exact hW hcon.1
      have hmem : p - t ∈ TranslationMarch.holes A N := by
        simp only [TranslationMarch.holes, TranslationMarch.blocked,
          Finset.mem_sdiff]
        exact ⟨Finset.mem_Icc.mpr ⟨h1, h2⟩, hW'⟩
      exact hmem
  · rintro (⟨⟨q, hq, rfl⟩, hp1, hpN⟩ | ⟨⟨hp1, hpN⟩, hW⟩)
    · refine ⟨⟨hp1, hpN⟩, ?_⟩
      have hqq : q + t - t = q := by ring
      rw [hqq]
      exact hmemW q hq
    · refine ⟨⟨by omega, hpN⟩, hW⟩

/-- The decomposition union is disjoint (t ≥ 0): propagated holes sit at
    positions ≥ 1+t, edge holes at positions ≤ t. -/
theorem march_unsat_disjoint_pos (A : Finset ℤ) (N t : ℤ) (ht : 0 ≤ t) :
    Disjoint ((TranslationMarch.holes A N).image (· + t) ∩ Finset.Icc 1 N)
      ((Finset.Icc 1 t).filter
        (fun p => p - t ∉ TranslationMarch.rawBlocked A)) := by
  rw [Finset.disjoint_left]
  rintro p hmem hflt
  rw [Finset.mem_inter, Finset.mem_image] at hmem
  obtain ⟨⟨q, hq, rfl⟩, -⟩ := hmem
  have hq1 : 1 ≤ q := by
    have hI : q ∈ Finset.Icc 1 N := by
      simp only [TranslationMarch.holes, Finset.mem_sdiff] at hq
      exact hq.1
    rw [Finset.mem_Icc] at hI
    exact hI.1
  have hflt' := hflt
  rw [Finset.mem_filter, Finset.mem_Icc] at hflt'
  omega

/-- The decomposition union is disjoint (t ≤ 0): propagated holes sit at
    positions ≤ N+t, edge holes at positions ≥ N+t+1. -/
theorem march_unsat_disjoint_neg (A : Finset ℤ) (N t : ℤ) (ht : t ≤ 0) :
    Disjoint ((TranslationMarch.holes A N).image (· + t) ∩ Finset.Icc 1 N)
      ((Finset.Icc (N + t + 1) N).filter
        (fun p => p - t ∉ TranslationMarch.rawBlocked A)) := by
  rw [Finset.disjoint_left]
  rintro p hmem hflt
  rw [Finset.mem_inter, Finset.mem_image] at hmem
  obtain ⟨⟨q, hq, rfl⟩, -⟩ := hmem
  have hqN : q ≤ N := by
    have hI : q ∈ Finset.Icc 1 N := by
      simp only [TranslationMarch.holes, Finset.mem_sdiff] at hq
      exact hq.1
    rw [Finset.mem_Icc] at hI
    exact hI.2
  have hflt' := hflt
  rw [Finset.mem_filter, Finset.mem_Icc] at hflt'
  omega

/-- Corollary (Propagation): every rigidly translated hole still inside
    [1,N] is a hole of A+t. Needs no nonemptiness. -/
theorem propagation_subset (A : Finset ℤ) (N t : ℤ) :
    (TranslationMarch.holes A N).image (· + t) ∩ Finset.Icc 1 N
      ⊆ TranslationMarch.holes (A.image (· + t)) N := by
  rw [holes_filter]
  intro p hp
  rw [Finset.mem_inter, Finset.mem_image] at hp
  obtain ⟨⟨q, hq, rfl⟩, hpI⟩ := hp
  rw [Finset.mem_filter]
  refine ⟨hpI, ?_⟩
  have hqW : q ∉ TranslationMarch.rawBlocked A := by
    simp only [TranslationMarch.holes, TranslationMarch.blocked,
      Finset.mem_sdiff, Finset.mem_inter] at hq
    exact fun hw => hq.2 ⟨hw, hq.1⟩
  have hqq : q + t - t = q := by ring
  rw [hqq]
  exact hqW

/-- Corollary (Rescue threshold), t ≥ 0: the propagation term is empty
    exactly when t > N − min(holes(A)). -/
theorem rescue_threshold_pos (A : Finset ℤ) (N t : ℤ) (ht : 0 ≤ t)
    (hne : (TranslationMarch.holes A N).Nonempty) :
    (TranslationMarch.holes A N).image (· + t) ∩ Finset.Icc 1 N = ∅
      ↔ N < (TranslationMarch.holes A N).min' hne + t := by
  have hsub : TranslationMarch.holes A N ⊆ Finset.Icc 1 N := Finset.sdiff_subset
  have hmem : ∀ q : ℤ, q ∈ TranslationMarch.holes A N → 1 ≤ q := by
    intro q hq
    have hI := hsub hq
    rw [Finset.mem_Icc] at hI
    exact hI.1
  rw [Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have hmin_mem := Finset.min'_mem (TranslationMarch.holes A N) hne
    have hI : (TranslationMarch.holes A N).min' hne + t ∈ Finset.Icc 1 N := by
      rw [Finset.mem_Icc]
      exact ⟨by have := hmem _ hmin_mem; omega, by omega⟩
    have himg : (TranslationMarch.holes A N).min' hne + t
        ∈ (TranslationMarch.holes A N).image (· + t) := by
      rw [Finset.mem_image]
      exact ⟨_, hmin_mem, rfl⟩
    exact h _ (Finset.mem_inter.mpr ⟨himg, hI⟩)
  · intro hlt p hp
    rw [Finset.mem_inter, Finset.mem_image] at hp
    obtain ⟨⟨q, hq, rfl⟩, hpI⟩ := hp
    rw [Finset.mem_Icc] at hpI
    have hle := Finset.min'_le (TranslationMarch.holes A N) q hq
    omega

/-- Corollary (Rescue threshold), t ≤ 0: symmetric, with max(holes(A)). -/
theorem rescue_threshold_neg (A : Finset ℤ) (N t : ℤ) (ht : t ≤ 0)
    (hne : (TranslationMarch.holes A N).Nonempty) :
    (TranslationMarch.holes A N).image (· + t) ∩ Finset.Icc 1 N = ∅
      ↔ (TranslationMarch.holes A N).max' hne + t < 1 := by
  have hsub : TranslationMarch.holes A N ⊆ Finset.Icc 1 N := Finset.sdiff_subset
  have hmem : ∀ q : ℤ, q ∈ TranslationMarch.holes A N → q ≤ N := by
    intro q hq
    have hI := hsub hq
    rw [Finset.mem_Icc] at hI
    exact hI.2
  rw [Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have hmax_mem := Finset.max'_mem (TranslationMarch.holes A N) hne
    have hI : (TranslationMarch.holes A N).max' hne + t ∈ Finset.Icc 1 N := by
      rw [Finset.mem_Icc]
      exact ⟨by omega, by have := hmem _ hmax_mem; omega⟩
    have himg : (TranslationMarch.holes A N).max' hne + t
        ∈ (TranslationMarch.holes A N).image (· + t) := by
      rw [Finset.mem_image]
      exact ⟨_, hmax_mem, rfl⟩
    exact h _ (Finset.mem_inter.mpr ⟨himg, hI⟩)
  · intro hlt p hp
    rw [Finset.mem_inter, Finset.mem_image] at hp
    obtain ⟨⟨q, hq, rfl⟩, hpI⟩ := hp
    rw [Finset.mem_Icc] at hpI
    have hle := Finset.le_max' (TranslationMarch.holes A N) q hq
    omega

/-- Corollary (Additive bound), t ≥ 0: |holes(A+t)| ≤ |holes(A)| + |t|.
    The saturated bound |holes| ≤ |t| is NOT claimed (it fails in general). -/
theorem additive_bound_pos (A : Finset ℤ) (N t : ℤ)
    (hne : A.Nonempty) (hA : A ⊆ Finset.Icc 1 N)
    (hAt : A.image (· + t) ⊆ Finset.Icc 1 N) (ht : 0 ≤ t) :
    (TranslationMarch.holes (A.image (· + t)) N).card
      ≤ (TranslationMarch.holes A N).card + Int.natAbs t := by
  rw [march_unsat_pos A N t hne hA hAt ht,
    Finset.card_union_of_disjoint (march_unsat_disjoint_pos A N t ht)]
  have h1 : ((TranslationMarch.holes A N).image (· + t) ∩ Finset.Icc 1 N).card
      ≤ (TranslationMarch.holes A N).card :=
    calc ((TranslationMarch.holes A N).image (· + t) ∩ Finset.Icc 1 N).card
        ≤ ((TranslationMarch.holes A N).image (· + t)).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = (TranslationMarch.holes A N).card :=
          Finset.card_image_of_injective _ (injective_add_right t)
  have h2 : ((Finset.Icc 1 t).filter
      (fun p => p - t ∉ TranslationMarch.rawBlocked A)).card ≤ Int.natAbs t :=
    calc ((Finset.Icc 1 t).filter
        (fun p => p - t ∉ TranslationMarch.rawBlocked A)).card
        ≤ (Finset.Icc 1 t).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = Int.natAbs t := by
          rw [Int.card_Icc]
          omega
  omega

/-- Corollary (Additive bound), t ≤ 0. -/
theorem additive_bound_neg (A : Finset ℤ) (N t : ℤ)
    (hne : A.Nonempty) (hA : A ⊆ Finset.Icc 1 N)
    (hAt : A.image (· + t) ⊆ Finset.Icc 1 N) (ht : t ≤ 0) :
    (TranslationMarch.holes (A.image (· + t)) N).card
      ≤ (TranslationMarch.holes A N).card + Int.natAbs t := by
  rw [march_unsat_neg A N t hne hA hAt ht,
    Finset.card_union_of_disjoint (march_unsat_disjoint_neg A N t ht)]
  have h1 : ((TranslationMarch.holes A N).image (· + t) ∩ Finset.Icc 1 N).card
      ≤ (TranslationMarch.holes A N).card :=
    calc ((TranslationMarch.holes A N).image (· + t) ∩ Finset.Icc 1 N).card
        ≤ ((TranslationMarch.holes A N).image (· + t)).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = (TranslationMarch.holes A N).card :=
          Finset.card_image_of_injective _ (injective_add_right t)
  have h2 : ((Finset.Icc (N + t + 1) N).filter
      (fun p => p - t ∉ TranslationMarch.rawBlocked A)).card ≤ Int.natAbs t :=
    calc ((Finset.Icc (N + t + 1) N).filter
        (fun p => p - t ∉ TranslationMarch.rawBlocked A)).card
        ≤ (Finset.Icc (N + t + 1) N).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = Int.natAbs t := by
          rw [Int.card_Icc]
          have h1 : (0:ℤ) ≤ -t := by omega
          omega
  omega

end TranslationMarchUnsat
