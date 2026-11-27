import TableDiagonal
import Mathlib.Order.Interval.Set.Union
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

open Set MeasureTheory Function
open scoped BigOperators
namespace SparseHalfGraphon

noncomputable def leftEndpoint (a : ℝ) (w : ℕ→ℝ) (i : ℕ) :=
  a+∑ j ∈ Finset.range i,w j

noncomputable def intervalCell (a : ℝ) (w : ℕ→ℝ) (i : ℕ) : Set ℝ :=
  Ico (leftEndpoint a w i) (leftEndpoint a w (i+1))

lemma left_succ (a : ℝ) (w : ℕ→ℝ) (i : ℕ) :
    leftEndpoint a w (i+1)=leftEndpoint a w i+w i := by
  unfold leftEndpoint
  rw [Finset.sum_range_succ]
  ring

lemma left_mono (a : ℝ) (w : ℕ→ℝ) (h : ∀ i, 0≤w i) :
    Monotone (leftEndpoint a w) :=
  monotone_nat_of_le_succ (fun i=>by rw [left_succ]; linarith [h i])

lemma cells_disjoint (a : ℝ) (w : ℕ→ℝ) (h : ∀ i, 0≤w i) :
    Pairwise (Disjoint on intervalCell a w) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hx' : leftEndpoint a w i≤x ∧ x<leftEndpoint a w (i+1) := hx
  have hy' : leftEndpoint a w j≤x ∧ x<leftEndpoint a w (j+1) := hy
  rcases lt_or_gt_of_ne hij with hh | hh
  · exact not_lt_of_ge ((left_mono a w h (Nat.succ_le_of_lt hh)).trans hy'.1) hx'.2
  · exact not_lt_of_ge ((left_mono a w h (Nat.succ_le_of_lt hh)).trans hx'.1) hy'.2

/-- Finite mass splitting by nested half-open intervals. Nonempty
and zero-mass children are handled by the same expression. -/
theorem cells_cover (a : ℝ) (w : ℕ→ℝ) (h : ∀ i, 0≤w i) (n:ℕ) :
    (⋃ i ∈ Finset.range n, intervalCell a w i)=Ico a (a+∑ j ∈ Finset.range n,w j) := by
  have h0 : leftEndpoint a w 0=a := by simp [leftEndpoint]
  apply le_antisymm
  · intro x hx
    rcases mem_iUnion.mp hx with ⟨i,hi⟩
    rcases mem_iUnion.mp hi with ⟨hi,hx⟩
    have hx' : leftEndpoint a w i≤x ∧ x<leftEndpoint a w (i+1) := hx
    have hi' := Finset.mem_range.mp hi
    refine ⟨?_,?_⟩
    · simpa [h0] using (left_mono a w h (Nat.zero_le i)).trans hx'.1
    · exact lt_of_lt_of_le hx'.2 (left_mono a w h (Nat.succ_le_of_lt hi'))
  · have hh := Ico_subset_biUnion_Ico n (leftEndpoint a w)
    rw [h0] at hh
    exact hh

theorem cell_volume (a : ℝ) (w : ℕ→ℝ) (h : ∀ i, 0≤w i) (i:ℕ) :
    volume.real (intervalCell a w i)=w i := by
  unfold intervalCell
  rw [Real.volume_real_Ico,left_succ,add_sub_cancel_left,max_eq_left (h i)]

#print axioms cells_cover
#print axioms cell_volume
end SparseHalfGraphon
