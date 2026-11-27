import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace SparseHalfComplementCore
open scoped BigOperators

variable {V E : Type*}

/-- An outside edge in a triangle-free graph has disjoint neighborhoods
toward the root set A. Count the anchors on neither endpoint's side. -/
theorem missingAnchors [DecidableEq V] (A X Y : Finset V)
    (hX : X ⊆ A) (hY : Y ⊆ A) (hXY : Disjoint X Y) :
    (A \ (X ∪ Y)).card + X.card + Y.card = A.card := by
  have hU : X ∪ Y ⊆ A := Finset.union_subset hX hY
  have hC := Finset.card_sdiff_of_subset hU
  have hle := Finset.card_le_card hU
  have hD := Finset.card_union_of_disjoint hXY
  omega

/-- In the saturated case every anchor belongs to exactly one endpoint
neighborhood. This implies a bipartition of the outside graph, by anchoring. -/
theorem oneNeighbor [DecidableEq V] (A X Y : Finset V)
    (hX : X ⊆ A) (hY : Y ⊆ A) (hXY : Disjoint X Y)
    (h2X : A.card ≤ 2 * X.card) (h2Y : A.card ≤ 2 * Y.card)
    {a : V} (ha : a ∈ A) :
    (a ∈ X ∧ a ∉ Y) ∨ (a ∈ Y ∧ a ∉ X) := by
  have h := missingAnchors A X Y hX hY hXY
  have hzero : (A \ (X ∪ Y)).card = 0 := by omega
  have hdis := Finset.disjoint_left.mp hXY
  by_cases hx : a ∈ X
  · exact Or.inl ⟨hx, fun hy => hdis hx hy⟩
  · right
    refine ⟨?_, hx⟩
    by_contra hy
    have hp : a ∈ A \ (X ∪ Y) := by simp [ha, hx, hy]
    have hmem := Finset.card_pos.mpr ⟨a, hp⟩
    omega

/-- The total number of monochromatic outside edges from all anchors is
exactly the total of the two-neighborhood mass deficits on the edges. -/
theorem sum_bad_eq_deficits [DecidableEq V] (A : Finset V) (edges : Finset E)
    (X Y : E → Finset V)
    (hX : ∀ e ∈ edges, X e ⊆ A) (hY : ∀ e ∈ edges, Y e ⊆ A)
    (hXY : ∀ e ∈ edges, Disjoint (X e) (Y e)) :
    (∑ a ∈ A, ∑ e ∈ edges, if a ∈ X e ∪ Y e then 0 else (1 : ℕ)) =
    ∑ e ∈ edges, (A.card - (X e).card - (Y e).card) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  have hsum : (∑ a ∈ A, if a ∈ X e ∪ Y e then 0 else (1 : ℕ)) =
      (A \ (X e ∪ Y e)).card := by
    have hf : (A.filter fun z => z ∉ X e ∪ Y e) = A \ (X e ∪ Y e) := by ext; simp
    rw [← hf, Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : a ∈ X e ∪ Y e <;> simp [h]
  rw [hsum]
  have h := missingAnchors A (X e) (Y e) (hX e he) (hY e he) (hXY e he)
  omega

#print axioms oneNeighbor
#print axioms sum_bad_eq_deficits
end SparseHalfComplementCore
