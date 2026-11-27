import GeometricGramChartStep

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory Set
open scoped ENNReal InnerProductSpace

noncomputable def finBorderEquiv (k : ℕ) : Fin k⊕Unit ≃ Fin (k+1) :=
  (Equiv.sumCongr (Equiv.refl _) finOneEquiv.symm).trans finSumFinEquiv

@[simp] theorem finBorder_inl (k : ℕ) (i : Fin k) :
    finBorderEquiv k (.inl i)= i.castSucc := rfl

@[simp] theorem finBorder_inr (k : ℕ) (u : Unit) :
    finBorderEquiv k (.inr u)= Fin.last k := by
  rfl

theorem gramChart_border (k : ℕ) (x : PairCoord (Fin (k+1))→ℝ) :
    (gramChart x).submatrix (finBorderEquiv k) (finBorderEquiv k) =
      pageBorder (gramChart (chartStep k x).1) (chartStep k x).2 := by
  ext i j
  rcases i with i|i <;> rcases j with j|j
  · simp only [Matrix.submatrix_apply,finBorder_inl,pageBorder,Matrix.fromBlocks_apply₁₁,
      chartStep_coords]
    by_cases h : i < j
    · simp [gramChart,h,pairStepMap]
    · by_cases t : j < i
      · simp [gramChart,h,t,pairStepMap]
      · simp [gramChart,h,t,pairStepMap]
  · simp [Matrix.submatrix_apply,finBorder_inl,finBorder_inr,pageBorder,Matrix.fromBlocks_apply₁₂,
      pageCol,chartStep_coords,gramChart,pairStepMap]
  · simp [Matrix.submatrix_apply,finBorder_inl,finBorder_inr,pageBorder,Matrix.fromBlocks_apply₂₁,
      pageCol,chartStep_coords,gramChart,pairStepMap,not_lt_of_ge (Fin.le_last j.castSucc)]
  · cases i
    cases j
    simp [Matrix.submatrix_apply,finBorder_inr,pageBorder,Matrix.fromBlocks_apply₂₂,gramChart]

theorem gramChart_border_det (k : ℕ) (x : PairCoord (Fin (k+1))→ℝ) :
    (gramChart x).det = (pageBorder (gramChart (chartStep k x).1) (chartStep k x).2).det := by
  rw [← gramChart_border,Matrix.det_submatrix_equiv_self]

theorem gramChart_border_pd (k : ℕ) (x : PairCoord (Fin (k+1))→ℝ) :
    (gramChart x).PosDef ↔ (pageBorder (gramChart (chartStep k x).1) (chartStep k x).2).PosDef := by
  rw [← gramChart_border]
  constructor
  · exact fun h => h.submatrix (finBorderEquiv k).injective
  · intro h
    simpa using h.submatrix (finBorderEquiv k).symm.injective

#print axioms gramChart_border
end RobustFolkman.GeometricGap
