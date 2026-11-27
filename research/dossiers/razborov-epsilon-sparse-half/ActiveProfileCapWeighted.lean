import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace SparseHalfActiveProfileWeighted

open Finset

variable {V : Type*} [DecidableEq V]
open scoped BigOperators
variable (w : V → ℝ) (hw : ∀ z, 0 ≤ w z)
def mass (A : Finset V) := ∑ z ∈ A, w z

theorem mass_union {U W : Finset V} (h : Disjoint U W) :
    mass w (U ∪ W) = mass w U + mass w W := by
  exact Finset.sum_union h

include hw

/-- Two subsets larger in total than the ambient set must meet. -/
theorem common_anchor {R U W : Finset V}
    (hU : U ⊆ R) (hW : W ⊆ R) (hlarge : mass w R < mass w U + mass w W) :
    ∃ z, z ∈ U ∧ z ∈ W := by
  by_contra! h
  have hd : Disjoint U W := Finset.disjoint_left.mpr (fun {z} hx hy => h z hx hy)
  have hc : mass w (U ∪ W) ≤ mass w R :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.union_subset hU hW) (fun z _ _ => hw z)
  rw [mass_union w hd] at hc
  exact (not_lt_of_ge hc) hlarge

/-- A graph primitive for the cut-limit argument: large rows into a
nearly complete template create exact nonedges, not just sparse rectangles. -/
theorem forbidden_adj {Adj : V → V → Prop}
    (htf : ∀ ⦃x y z : V⦄, Adj x y → Adj x z → ¬ Adj y z)
    {x y : V} {R U W : Finset V}
    (hU : U ⊆ R) (hW : W ⊆ R) (hlarge : mass w R < mass w U + mass w W)
    (hx : ∀ z ∈ U, Adj x z) (hy : ∀ z ∈ W, Adj y z) :
    ¬ Adj x y := by
  rintro hxy
  obtain ⟨z, hz, hz'⟩ := common_anchor w hw hU hW hlarge
  exact htf hxy (hx z hz) (hy z hz')

/-- If active vertices X have overlapping anchor rows in S and intersect
all nearly full rows from T into Q, then X ∪ T is an independent set. -/
theorem active_cap {Adj : V → V → Prop}
    (htf : ∀ ⦃x y z : V⦄, Adj x y → Adj x z → ¬ Adj y z)
    (symm : ∀ ⦃x y⦄, Adj x y → Adj y x)
    (maxIndependent : ℝ)
    (hmax : ∀ Z : Finset V, (∀ x ∈ Z, ∀ y ∈ Z, ¬ Adj x y) →
      mass w Z ≤ maxIndependent)
    (X T S Q : Finset V) (hxT : Disjoint X T)
    (hT : ∀ x ∈ T, ∀ y ∈ T, ¬ Adj x y)
    (NS NQ : V → Finset V)
    (hS : ∀ z, NS z ⊆ S) (hQ : ∀ z, NQ z ⊆ Q)
    (hAS : ∀ z w, w ∈ NS z → Adj z w)
    (hAQ : ∀ z w, w ∈ NQ z → Adj z w)
    (hbig : ∀ x ∈ X, mass w S < 2 * mass w (NS x))
    (hcover : ∀ x ∈ X, ∀ y ∈ T, mass w Q < mass w (NQ x) + mass w (NQ y)) :
    mass w X + mass w T ≤ maxIndependent := by
  rw [← mass_union w hxT]
  apply hmax
  intro x hx y hy
  simp only [Finset.mem_union] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · have h1 := hbig x hx
    have h2 := hbig y hy
    exact forbidden_adj w hw htf (hS x) (hS y) (by linarith) (hAS x) (hAS y)
  · exact forbidden_adj w hw htf (hQ x) (hQ y) (hcover x hx y hy) (hAQ x) (hAQ y)
  · exact fun he =>
      forbidden_adj w hw htf (hQ y) (hQ x) (hcover y hy x hx) (hAQ y) (hAQ x) (symm he)
  · exact hT x hx y hy

#print axioms active_cap
end SparseHalfActiveProfileWeighted
