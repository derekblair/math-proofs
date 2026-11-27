import IntervalCells
import Mathlib.Data.Fintype.EquivFin

open Set MeasureTheory Function
open scoped BigOperators
namespace SparseHalfGraphon

variable {I : Type*} [Fintype I]

noncomputable def extendLengths (w : I → ℝ) (n : ℕ) :=
  if h : n < Fintype.card I then w ((Fintype.equivFin I).symm ⟨n,h⟩) else 0

noncomputable def finiteCellLeft (a : ℝ) (w : I → ℝ) (i : I) :=
  leftEndpoint a (extendLengths w) ((Fintype.equivFin I i).val)

lemma extendLengths_nonneg (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (n : ℕ) :
    0 ≤ extendLengths w n := by
  unfold extendLengths
  split
  · exact hw _
  · rfl

lemma extendLengths_apply (w : I → ℝ) (i : I) :
    extendLengths w ((Fintype.equivFin I i).val) = w i := by
  simp [extendLengths]

lemma finiteCell_eq (a : ℝ) (w : I → ℝ) (i : I) :
    Ico (finiteCellLeft a w i) (finiteCellLeft a w i + w i) =
    intervalCell a (extendLengths w) ((Fintype.equivFin I i).val) := by
  rw [intervalCell, left_succ, extendLengths_apply]
  rfl

/-- Split an interval into consecutive measurable intervals indexed by
any finite type, including empty families and zero-length members. -/
theorem finite_interval_split (a : ℝ) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∃ L : I → ℝ,
      Pairwise (Disjoint on fun i => Ico (L i) (L i + w i)) ∧
      (⋃ i, Ico (L i) (L i + w i)) = Ico a (a + ∑ i, w i) := by
  classical
  refine ⟨finiteCellLeft a w, ?_, ?_⟩
  · intro i j hij
    change Disjoint (Ico _ _) (Ico _ _)
    rw [finiteCell_eq, finiteCell_eq]
    apply cells_disjoint a (extendLengths w) (extendLengths_nonneg w hw)
    exact fun h => hij ((Fintype.equivFin I).injective (Fin.ext h))
  · simp_rw [finiteCell_eq]
    have hsum : ∑ i ∈ Finset.range (Fintype.card I), extendLengths w i = ∑ i, w i := by
      rw [← Fin.sum_univ_eq_sum_range]
      exact Fintype.sum_equiv (Fintype.equivFin I).symm _ _ (fun i => by simp [extendLengths])
    rw [← hsum, ← cells_cover a (extendLengths w)
      (extendLengths_nonneg w hw) (Fintype.card I)]
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨_,mem_iUnion.mpr ⟨Finset.mem_range.mpr (Fintype.equivFin I i).isLt, hi⟩⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      obtain ⟨his, hxi⟩ := mem_iUnion.mp hi
      let j : Fin (Fintype.card I) := ⟨i, Finset.mem_range.mp his⟩
      refine mem_iUnion.mpr ⟨(Fintype.equivFin I).symm j, ?_⟩
      simpa [j] using hxi

#print axioms finite_interval_split
end SparseHalfGraphon
