/-
  VoidMonoid.lean — R291/R296/R299 void-frame monoid: D2(c) repair + D3 tiling — pairwise-disjoint families are not closed under union; generated submonoid loses disjointness; maximal family tiles (Q-41 SURVIVES).

  Paper: papers/void-frames-defect-October-11-2026/
  Status: [PROVED] — d2c_not_closed, d2c_generated_loses_disjoint, maximal_family_tiles
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); R318: bakkie `lake build` exit 0, zero sorrys, axioms standard-only.
-/

import Mathproofs.VoidMonoidParam

/-!
# VoidMonoid: D2(c) repair + maximal-family tiling (R296/R299)

Paper trail: `~/workspace/math-unsolved/ROUND296_DOSSIER.md` (defect core D1/D2/D3),
`~/workspace/math-unsolved/ROUND299_DOSSIER.md` (D2(c) repair).
Rule-9 gates: Q-35 (R291 N′ base — Bunny, scoped SURVIVES) + Q-39 (D2(c) limited
OBJECTION, verbatim: `"does NOT form a nontrivial submonoid" needs qualification
({e,({2},∅)} is a nontrivial pairwise-disjoint submonoid, as D2(b) itself
establishes)`), Q-41 (D2(c) repair re-review — Angel, **SURVIVES**, 2026-10-11).
Stacked on `Mathproofs.VoidMonoidParam` (Q-42 SURVIVES): `Nprime`, `d`,
`defect_core` (D1), `fully_additive_submonoid` (D2(a)),
`disjoint_footprint_submonoid` (D2(b)-general).

Formalized here ([PROVED*]-grade, Lean-checked):
- `d2c_not_closed` — repaired D2(c), part 1: a pairwise-disjoint-footprint
  family with ≥2 non-identity elements is NOT closed under union (verbatim
  repair: "a pairwise-disjoint family with ≥2 nonidentity elements is not
  closed under union; its generated submonoid loses disjointness but is still
  a submonoid — fixes local wording, no classification change").
- `d2c_generated_loses_disjoint` — repaired D2(c), part 2: the generated
  submonoid `Submonoid.closure ↑F` is a submonoid by construction yet loses
  pairwise disjointness (witnessed by x and x*y inside it).
- `maximal_family_tiles` — D3's structural core, general: an inclusion-maximal
  pairwise-disjoint-footprint family contains the identity and its footprints
  cover every tag. The 40/8 census counts for W={2,3,4} are [COMPUTED]×2
  (r296 path1/2), NOT formalized here — no half-formalization.

R59/R63 audit: every direction-sensitive step is an exact set equality
(union/inter identities); zero "by inspection" monotone substitutions.

Lean 4.34.1 / Mathlib. Zero sorrys. Axioms: standard only (see ROUND318 dossier).
-/

open Finset
open VoidMonoidParam
open VoidMonoidParam.Nprime

namespace VoidMonoid

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Decidable equality on `Nprime α` (needed for `Finset.insert` on families).
    Not derived in `VoidMonoidParam`; proved here from the `@[ext]` lemma. -/
instance : DecidableEq (Nprime α) := fun x y =>
  match decEq x.A y.A, decEq x.B y.B with
  | isTrue hA, isTrue hB => isTrue (Nprime.ext hA hB)
  | isFalse hA, _ => isFalse (fun h => hA (congrArg Nprime.A h))
  | _, isFalse hB => isFalse (fun h => hB (congrArg Nprime.B h))

/-- Pairwise-disjoint-footprint predicate on a family (R296 §1). -/
def PairwiseDisj (F : Finset (Nprime α)) : Prop :=
  ∀ x ∈ F, ∀ y ∈ F, x ≠ y → x.A ∩ y.A = ∅

/-- A = ∅ forces the element to be the identity (contrapositive of
    `ne_one_imp_A_ne_empty`). -/
theorem eq_one_of_A_empty {x : Nprime α} (hA : x.A = ∅) : x = 1 := by
  have hB : x.B = ∅ := subset_empty_eq (hA ▸ x.hB)
  refine Nprime.ext ?_ ?_ <;> simp [hA, hB]

/-- Helper: x*y ≠ x for distinct non-identity x,y with disjoint footprints.
    The union footprint x.A ∪ y.A strictly contains x.A. -/
private theorem prod_ne_of_pairwise_disj (F : Finset (Nprime α))
    (hdisj : PairwiseDisj F)
    {x y : Nprime α} (hx : x ∈ F) (hy : y ∈ F) (hny : y ≠ 1) (hne : x ≠ y) :
    x * y ≠ x := by
  have hA2ne : y.A ≠ ∅ := ne_one_imp_A_ne_empty hny
  have hinter : x.A ∩ y.A = ∅ := hdisj x hx y hy hne
  intro h
  have hunion : x.A ∪ y.A = x.A := by rw [← mul_A, h]
  have hsub : y.A ⊆ x.A := by
    intro a ha
    have hmem : a ∈ x.A ∪ y.A := Finset.mem_union.mpr (Or.inr ha)
    rw [hunion] at hmem
    exact hmem
  apply hA2ne
  apply Finset.eq_empty_of_forall_notMem
  intro a ha
  have hmem : a ∈ x.A ∩ y.A := Finset.mem_inter.mpr ⟨hsub ha, ha⟩
  rw [hinter] at hmem
  exact Finset.notMem_empty a hmem

/-- D2(c) repair, part 1 (R299 §2, Bunny's verbatim repair): a
    pairwise-disjoint-footprint family with ≥2 non-identity elements is not
    closed under union. -/
theorem d2c_not_closed (F : Finset (Nprime α)) (hdisj : PairwiseDisj F)
    {x y : Nprime α} (hx : x ∈ F) (hy : y ∈ F)
    (hnx : x ≠ 1) (hny : y ≠ 1) (hne : x ≠ y) :
    x * y ∉ F := by
  have hA1 : x.A ≠ ∅ := ne_one_imp_A_ne_empty hnx
  have hne2 : x * y ≠ x := prod_ne_of_pairwise_disj F hdisj hx hy hny hne
  intro hmem
  have hdisj' := hdisj (x * y) hmem x hx hne2
  rw [mul_A] at hdisj'
  -- (x.A ∪ y.A) ∩ x.A = x.A ≠ ∅
  have key : (x.A ∪ y.A) ∩ x.A = x.A := by
    rw [Finset.inter_comm]
    exact inter_eq_self_of_subset Finset.subset_union_left
  rw [key] at hdisj'
  exact hA1 hdisj'

/-- D2(c) repair, part 2 (R299 §2): the generated submonoid
    `Submonoid.closure ↑F` is a submonoid by construction yet loses pairwise
    disjointness — witnessed by x and x*y inside it. -/
theorem d2c_generated_loses_disjoint (F : Finset (Nprime α)) (hdisj : PairwiseDisj F)
    {x y : Nprime α} (hx : x ∈ F) (hy : y ∈ F)
    (hnx : x ≠ 1) (hny : y ≠ 1) (hne : x ≠ y) :
    ∃ u v : Nprime α, u ∈ Submonoid.closure (↑F : Set (Nprime α)) ∧
      v ∈ Submonoid.closure (↑F : Set (Nprime α)) ∧ u ≠ v ∧ u.A ∩ v.A ≠ ∅ := by
  have hA1 : x.A ≠ ∅ := ne_one_imp_A_ne_empty hnx
  have hne2 : x * y ≠ x := prod_ne_of_pairwise_disj F hdisj hx hy hny hne
  refine ⟨x, x * y, Submonoid.subset_closure (Finset.mem_coe.mpr hx), ?_,
    fun h => hne2 h.symm, ?_⟩
  · exact Submonoid.mul_mem _ (Submonoid.subset_closure (Finset.mem_coe.mpr hx))
      (Submonoid.subset_closure (Finset.mem_coe.mpr hy))
  · rw [mul_A]
    have key : x.A ∩ (x.A ∪ y.A) = x.A :=
      inter_eq_self_of_subset Finset.subset_union_left
    rw [key]
    exact hA1

/-- D3's structural core, general (R296 §2 D3): an inclusion-maximal
    pairwise-disjoint-footprint family contains the identity and its footprints
    cover every tag (the annotated-set-partition form). -/
theorem maximal_family_tiles (F : Finset (Nprime α)) (hdisj : PairwiseDisj F)
    (hmax : ∀ G : Finset (Nprime α), PairwiseDisj G → F ⊆ G → G = F) :
    1 ∈ F ∧ Finset.univ ⊆ F.biUnion (fun z => z.A) := by
  constructor
  · -- the identity extends any family; maximality forces it in
    by_contra h1
    have hdisj' : PairwiseDisj (insert 1 F) := by
      intro a ha b hb hab
      simp only [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · simp [one_A]
      · simp [one_A]
      · exact hdisj a ha b hb hab
    have heq := hmax (insert 1 F) hdisj' (Finset.subset_insert 1 F)
    apply h1
    rw [← heq]
    exact Finset.mem_insert_self 1 F
  · -- if some tag w is uncovered, the singleton ({w},∅) extends F
    by_contra hcov
    rw [Finset.not_subset] at hcov
    obtain ⟨w, _, hw⟩ := hcov
    rw [Finset.mem_biUnion] at hw
    push_neg at hw
    -- hw : ∀ z ∈ F, w ∉ z.A
    obtain ⟨e, heA, -⟩ : ∃ e : Nprime α, e.A = {w} ∧ e.B = ∅ :=
      ⟨⟨{w}, ∅, Finset.empty_subset _⟩, rfl, rfl⟩
    have heF : e ∉ F := by
      intro hmem
      apply hw e hmem
      rw [heA]
      exact Finset.mem_singleton_self w
    have hdisj' : PairwiseDisj (insert e F) := by
      intro a ha b hb hab
      simp only [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · have hwb : w ∉ b.A := hw b hb
        rw [heA]
        exact Finset.disjoint_iff_inter_eq_empty.mp
          (Finset.disjoint_singleton_left.mpr hwb)
      · have hwa : w ∉ a.A := hw a ha
        rw [Finset.inter_comm, heA]
        exact Finset.disjoint_iff_inter_eq_empty.mp
          (Finset.disjoint_singleton_left.mpr hwa)
      · exact hdisj a ha b hb hab
    have heq := hmax (insert e F) hdisj' (Finset.subset_insert e F)
    apply heF
    rw [← heq]
    exact Finset.mem_insert_self e F

end VoidMonoid
