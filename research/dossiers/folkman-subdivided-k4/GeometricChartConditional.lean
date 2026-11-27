import GeometricChartWeight

namespace RobustFolkman.GeometricGap
open MeasureTheory Matrix Set
open scoped ENNReal InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

noncomputable def projectionMass (k m : ℕ) : ℝ≥0∞ :=
  ∫⁻ y in (projectionBall : Set (Fin k→ℝ)), projectionFactor m y

theorem ellipsoid_measurable {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) : MeasurableSet {y | anchorQuad A y<1} := by
  have q : Continuous (anchorQuad A) := by
    unfold anchorQuad
    simp only [dotProduct, Matrix.mulVec]
    apply continuous_finsetSum _ fun i _ => Continuous.mul (continuous_apply i) ?_
    exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  exact (isOpen_lt q continuous_const).measurableSet

/-- The actual conditional law, multiplied by the old Gram weight, is
the new chart density integrated over exactly the added coordinate fiber. -/
theorem chart_conditional_weight (k m : ℕ) (dim : Module.finrank ℝ E=k+m+2)
    (v : Fin k→UnitSphere E) (vi : LinearIndependent ℝ (fun i => (v i).val))
    (f : (PairCoord (Fin (k+1))→ℝ)→ℝ≥0∞) (fm : Measurable f) :
    let u := sampleChart v
    chartWeight k (m+1) u *
      (∫⁻ x : UnitSphere E, f (sampleChart (Fin.snoc (α:=fun _ => UnitSphere E) v x))
        ∂uniformSphere (volume : Measure E)) =
      (∫⁻ y : Fin k→ℝ, chartWeight (k+1) m ((chartStep k).symm (u,y)) *
        f ((chartStep k).symm (u,y))) / projectionMass k m := by
  intro u
  have A : gramChart u = anchorGram (fun i => (v i).val) := sampleChart_matrix v
  have pos : (gramChart u).PosDef := by
    rw [A]
    exact Matrix.posDef_gram_of_linearIndependent vi
  let g : (Fin k→ℝ)→ℝ≥0∞ := fun y => f ((chartStep k).symm (u,y))
  have gm : Measurable g := fm.comp ((chartStep k).symm.measurable.comp
    (measurable_const.prodMk measurable_id))
  have eq (x : UnitSphere E) :
      f (sampleChart (Fin.snoc (α:=fun _ => UnitSphere E) v x)) =
      g (fun i => ⟪(v i).val,x.val⟫_ℝ) := by
    unfold g
    congr 1
    apply (chartStep k).injective
    rw [sampleChart_snoc,(chartStep k).apply_symm_apply]
  simp_rw [eq]
  have law := sphere_fixed_anchor_conditional (fun i => (v i).val) vi m
    (by simpa using dim) g gm
  dsimp only at law
  rw [← A] at law
  rw [law]
  simp only [projectionMass,div_eq_mul_inv,←mul_assoc]
  congr 1
  rw [← lintegral_const_mul' _ _ (chartWeight_finite _ _ _)]
  let s : Set (Fin k→ℝ) := {y | anchorQuad (gramChart u) y<1}
  let w : (Fin k→ℝ)→ℝ≥0∞ := fun y =>
    chartWeight k (m+1) u *
      (ENNReal.ofReal ((Real.sqrt (gramChart u).det)⁻¹) *
        (g y)*ENNReal.ofReal ((Real.sqrt (1-anchorQuad (gramChart u) y))^m))
  have As : MeasurableSet s := ellipsoid_measurable _
  change (∫⁻ y in s, w y) = _
  rw [← lintegral_indicator As]
  apply lintegral_congr
  intro y
  rw [chartWeight_split k m u y pos]
  by_cases hs : y∈s
  · rw [indicator_of_mem hs,if_pos (show anchorQuad (gramChart u) y < 1 from hs)]
    unfold w g
    ac_rfl
  · rw [indicator_of_notMem hs,if_neg (show ¬anchorQuad (gramChart u) y < 1 from hs),zero_mul]

#print axioms chart_conditional_weight
end RobustFolkman.GeometricGap
