/-
  HoleSuppression.lean — R199 hole-suppression: T2 finite-set lemmas + T5 saturation theorems (two-margin dichotomy, subsingleton uniqueness, σ-saturation).

  Paper: papers/hole-suppression-absorption-October-11-2026/
  Status: [PROVED] — t2_iff, t5_saturation, t5_double_saturation, dichotomy_two_margins
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); R234: local + bakkie `lake build` exit 0, zero sorrys, axioms standard-only.
-/

/-
R199 — Hole suppression: T2 dichotomy + T5 saturation forcing (ROUND222, Lane 4).

Claims formalised (machine-checked; ROUND199_DOSSIER.md §§2,7):
- T2 (Suppression dichotomy, [PROVED*]→[PROVED]): a demands-holding pair is
  hole-capable ⟺ at least two margins are non-singleton. Machine-checked as
  the finite-set lemma `t2_iff`: there exist two distinct full-margin subsets
  of α × β ⟺ both margins have card > 1.
- T5 (Saturation forcing, [PROVED*]→[PROVED]): a saturated fibre carried by a
  bijection has no hole — machine-checked as `t5_saturation` (bijective maps
  send `univ` to `univ`), `t5_double_saturation`, and `t5_sigma_one`.
T3's witness and the T4 surveys stay [COMPUTED]; cited, not formalised.

Checked: Lean 4.34.1 + Mathlib v4.34.1, `lake build`, zero sorrys,
`#print axioms` standard-only (propext, Classical.choice, Quot.sound).
-/
import Mathlib

namespace HoleSuppression

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β]

/-- A subset of the product has full margins — the R199 fibre-pair margin condition
    πᵢ(X_r) = πᵢ(Y_r) restricted to one hole-pattern set. -/
def FullMargin (S : Finset (α × β)) : Prop :=
  S.image Prod.fst = Finset.univ ∧ S.image Prod.snd = Finset.univ

/-- T2, constructive direction: two non-singleton margins admit two distinct
    full-margin sets — the two "diagonals", with every off-diagonal point carried
    along on a fixed fibre (R199 §2 proof of T2). -/
theorem dichotomy_two_margins (a b : α) (hab : a ≠ b)
    (c d : β) (hcd : c ≠ d) :
    ∃ S T : Finset (α × β), FullMargin S ∧ FullMargin T ∧ S ≠ T := by
  refine ⟨(Finset.univ ×ˢ {c}) ∪ ({a} ×ˢ Finset.univ),
          (Finset.univ ×ˢ {d}) ∪ ({b} ×ˢ Finset.univ), ?_, ?_, ?_⟩
  · -- S has full margins: every x hits (x,c), every y hits (a,y)
    constructor
    · apply Finset.eq_univ_of_forall
      intro x
      rw [Finset.mem_image]
      exact ⟨(x, c),
        Finset.mem_union.mpr (Or.inl (Finset.mem_product.mpr
          ⟨Finset.mem_univ x, Finset.mem_singleton_self c⟩)),
        rfl⟩
    · apply Finset.eq_univ_of_forall
      intro y
      rw [Finset.mem_image]
      exact ⟨(a, y),
        Finset.mem_union.mpr (Or.inr (Finset.mem_product.mpr
          ⟨Finset.mem_singleton_self a, Finset.mem_univ y⟩)),
        rfl⟩
  · -- T has full margins: every x hits (x,d), every y hits (b,y)
    constructor
    · apply Finset.eq_univ_of_forall
      intro x
      rw [Finset.mem_image]
      exact ⟨(x, d),
        Finset.mem_union.mpr (Or.inl (Finset.mem_product.mpr
          ⟨Finset.mem_univ x, Finset.mem_singleton_self d⟩)),
        rfl⟩
    · apply Finset.eq_univ_of_forall
      intro y
      rw [Finset.mem_image]
      exact ⟨(b, y),
        Finset.mem_union.mpr (Or.inr (Finset.mem_product.mpr
          ⟨Finset.mem_singleton_self b, Finset.mem_univ y⟩)),
        rfl⟩
  · -- S ≠ T: (a,c) is in S but in neither arm of T
    intro hST
    have hmemS : (a, c) ∈ (Finset.univ ×ˢ {c}) ∪ ({a} ×ˢ Finset.univ) :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_product.mpr
        ⟨Finset.mem_univ a, Finset.mem_singleton_self c⟩))
    rw [hST] at hmemS
    rcases Finset.mem_union.mp hmemS with h1 | h2
    · rw [Finset.mem_product, Finset.mem_singleton] at h1
      exact hcd h1.2
    · rw [Finset.mem_product, Finset.mem_singleton] at h2
      exact hab h2.1

/-- T2, uniqueness direction (α-margin): a subsingleton first margin forces at
    most one full-margin set — no hole potential (R199 §2 proof of T2). -/
theorem uniqueness_of_subsingleton [Subsingleton α] (S T : Finset (α × β))
    (hS : FullMargin S) (hT : FullMargin T) : S = T := by
  ext p
  obtain ⟨x, z⟩ := p
  constructor
  · intro hp
    have hz : ∃ q ∈ T, Prod.snd q = z := by
      have hmem : z ∈ Finset.univ := Finset.mem_univ z
      rw [← hT.2] at hmem
      exact Finset.mem_image.mp hmem
    obtain ⟨⟨y, w⟩, hqw, hqz⟩ := hz
    have hyx : y = x := Subsingleton.elim y x
    have hwz : w = z := hqz
    rw [hyx, hwz] at hqw
    exact hqw
  · intro hp
    have hz : ∃ q ∈ S, Prod.snd q = z := by
      have hmem : z ∈ Finset.univ := Finset.mem_univ z
      rw [← hS.2] at hmem
      exact Finset.mem_image.mp hmem
    obtain ⟨⟨y, w⟩, hqw, hqz⟩ := hz
    have hyx : y = x := Subsingleton.elim y x
    have hwz : w = z := hqz
    rw [hyx, hwz] at hqw
    exact hqw

/-- T2, uniqueness direction (β-margin): symmetric in the second margin. -/
theorem uniqueness_of_subsingleton_beta [Subsingleton β] (S T : Finset (α × β))
    (hS : FullMargin S) (hT : FullMargin T) : S = T := by
  ext p
  obtain ⟨x, z⟩ := p
  constructor
  · intro hp
    have hx : ∃ q ∈ T, Prod.fst q = x := by
      have hmem : x ∈ Finset.univ := Finset.mem_univ x
      rw [← hT.1] at hmem
      exact Finset.mem_image.mp hmem
    obtain ⟨⟨y, w⟩, hqw, hqx⟩ := hx
    have hwz : w = z := Subsingleton.elim w z
    have hyx : y = x := hqx
    rw [hyx, hwz] at hqw
    exact hqw
  · intro hp
    have hx : ∃ q ∈ S, Prod.fst q = x := by
      have hmem : x ∈ Finset.univ := Finset.mem_univ x
      rw [← hS.1] at hmem
      exact Finset.mem_image.mp hmem
    obtain ⟨⟨y, w⟩, hqw, hqx⟩ := hx
    have hwz : w = z := Subsingleton.elim w z
    have hyx : y = x := hqx
    rw [hyx, hwz] at hqw
    exact hqw

/-- A Fintype with card ≤ 1 is a subsingleton. -/
theorem subsingleton_of_card_le_one (h : Fintype.card α ≤ 1) : Subsingleton α := by
  rwa [Fintype.card_le_one_iff_subsingleton] at h

/-- T2 (R199 Suppression dichotomy): hole-capable ⟺ ≥ 2 non-singleton margins.
    There are two distinct full-margin hole-pattern sets iff both margins have
    more than one element. -/
theorem t2_iff :
    (∃ S T : Finset (α × β), FullMargin S ∧ FullMargin T ∧ S ≠ T) ↔
      1 < Fintype.card α ∧ 1 < Fintype.card β := by
  constructor
  · rintro ⟨S, T, hS, hT, hne⟩
    refine ⟨?_, ?_⟩ <;> by_contra hlt <;> rw [not_lt] at hlt
    · exact hne (@uniqueness_of_subsingleton _ _ _ _ _ _
        (subsingleton_of_card_le_one hlt) S T hS hT)
    · exact hne (@uniqueness_of_subsingleton_beta _ _ _ _ _ _
        (subsingleton_of_card_le_one hlt) S T hS hT)
  · rintro ⟨ha, hb⟩
    obtain ⟨a⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card α)
    obtain ⟨b, hab⟩ := Fintype.exists_ne_of_one_lt_card ha a
    obtain ⟨c⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card β)
    obtain ⟨d, hcd⟩ := Fintype.exists_ne_of_one_lt_card hb c
    exact dichotomy_two_margins b a hab d c hcd

/-- Suppression coefficient: 1 = suppressed (pair agrees), 0 = hole realized. -/
def sigma {γ : Type*} [DecidableEq γ] (X Y : Finset γ) : ℕ :=
  if X = Y then 1 else 0

/-- T5(a) (R199 Saturation forcing): a bijection sends the saturated fibre to
    itself — X_r = A_r(S_r) = S_r = Y_r, so no hole on a saturated fibre. -/
theorem t5_saturation {γ : Type*} [DecidableEq γ] [Fintype γ] (f : γ → γ)
    (hf : Function.Bijective f) :
    Finset.univ.image f = Finset.univ := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, rfl⟩
    trivial
  · intro _
    obtain ⟨a, ha⟩ := hf.2 x
    exact ⟨a, ha⟩

/-- T5(b) (double saturation): X = A '' (univ), Y = univ with A bijective ⟹ X = Y. -/
theorem t5_double_saturation {γ : Type*} [DecidableEq γ] [Fintype γ] (f : γ → γ)
    (hf : Function.Bijective f) (X Y : Finset γ)
    (hX : X = Finset.univ.image f) (hY : Y = Finset.univ) : X = Y := by
  rw [hX, hY, t5_saturation f hf]

/-- T5 corollary: saturation forcing gives σ = 1 (the pair is suppressed). -/
theorem t5_sigma_one {γ : Type*} [DecidableEq γ] [Fintype γ] (f : γ → γ)
    (hf : Function.Bijective f) (X Y : Finset γ)
    (hX : X = Finset.univ.image f) (hY : Y = Finset.univ) :
    sigma X Y = 1 := by
  rw [t5_double_saturation f hf X Y hX hY]
  unfold sigma
  simp

end HoleSuppression
