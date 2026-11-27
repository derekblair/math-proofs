import Mathlib.Data.Finset.Card

namespace SparseHalfActiveProfile

open Finset

variable {V : Type*} [DecidableEq V]

/-- Two subsets larger in total than the ambient set must meet. -/
theorem common_anchor {R U W : Finset V}
    (hU : U ⊆ R) (hW : W ⊆ R) (hlarge : R.card < U.card + W.card) :
    ∃ z, z ∈ U ∧ z ∈ W := by
  by_contra! h
  have hd : Disjoint U W := Finset.disjoint_left.mpr (fun {z} hx hy => h z hx hy)
  have hc := Finset.card_le_card (Finset.union_subset hU hW)
  rw [Finset.card_union_of_disjoint hd] at hc
  omega

/-- A graph primitive for the cut-limit argument: large rows into a
nearly complete template create exact nonedges, not just sparse rectangles. -/
theorem forbidden_adj {Adj : V → V → Prop}
    (htf : ∀ ⦃x y z : V⦄, Adj x y → Adj x z → ¬ Adj y z)
    {x y : V} {R U W : Finset V}
    (hU : U ⊆ R) (hW : W ⊆ R) (hlarge : R.card < U.card + W.card)
    (hx : ∀ z ∈ U, Adj x z) (hy : ∀ z ∈ W, Adj y z) :
    ¬ Adj x y := by
  rintro hxy
  obtain ⟨z, hz, hz'⟩ := common_anchor hU hW hlarge
  exact htf hxy (hx z hz) (hy z hz')

/-- If active vertices X have overlapping anchor rows in S and intersect
all nearly full rows from T into Q, then X ∪ T is an independent set. -/
theorem active_cap {Adj : V → V → Prop}
    (htf : ∀ ⦃x y z : V⦄, Adj x y → Adj x z → ¬ Adj y z)
    (symm : ∀ ⦃x y⦄, Adj x y → Adj y x)
    (maxIndependent : ℕ)
    (hmax : ∀ Z : Finset V, (∀ x ∈ Z, ∀ y ∈ Z, ¬ Adj x y) →
      Z.card ≤ maxIndependent)
    (X T S Q : Finset V) (hxT : Disjoint X T)
    (hT : ∀ x ∈ T, ∀ y ∈ T, ¬ Adj x y)
    (NS NQ : V → Finset V)
    (hS : ∀ z, NS z ⊆ S) (hQ : ∀ z, NQ z ⊆ Q)
    (hAS : ∀ z w, w ∈ NS z → Adj z w)
    (hAQ : ∀ z w, w ∈ NQ z → Adj z w)
    (hbig : ∀ x ∈ X, S.card < 2 * (NS x).card)
    (hcover : ∀ x ∈ X, ∀ y ∈ T, Q.card < (NQ x).card + (NQ y).card) :
    X.card + T.card ≤ maxIndependent := by
  rw [← Finset.card_union_of_disjoint hxT]
  apply hmax
  intro x hx y hy
  simp only [Finset.mem_union] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · have h1 := hbig x hx
    have h2 := hbig y hy
    exact forbidden_adj htf (hS x) (hS y) (by omega) (hAS x) (hAS y)
  · exact forbidden_adj htf (hQ x) (hQ y) (hcover x hx y hy) (hAQ x) (hAQ y)
  · exact fun he =>
      forbidden_adj htf (hQ y) (hQ x) (hcover y hy x hx) (hAQ y) (hAQ x) (symm he)
  · exact hT x hx y hy

#print axioms active_cap
end SparseHalfActiveProfile
