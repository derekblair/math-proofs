import GeometricGramFiber

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- The actual joint Gram-coordinate density of an iid tuple of normalized
Haar sphere points. The normalizing constant is finite, positive, and
independent of the measurable weight under test. -/
theorem spherical_joint_gram_weighted (n m : ℕ)
    (dim : Module.finrank ℝ E=n+m+1) :
    ∃ C : ℝ≥0∞, C≠0 ∧ C≠∞ ∧
      ∀ f : (PairCoord (Fin n)→ℝ)→ℝ≥0∞, Measurable f →
      (∫⁻ v : Fin n→UnitSphere E, f (sampleChart v)
        ∂(Measure.pi fun _ : Fin n => uniformSphere (volume : Measure E))) =
        C * ∫⁻ x, chartWeight n m x * f x := by
  let μ := uniformSphere (volume : Measure E)
  letI : IsProbabilityMeasure μ := uniformSphere_isProbability _
  induction n generalizing m with
  | zero =>
    refine ⟨1,one_ne_zero,ENNReal.one_ne_top,?_⟩
    intro f _
    let x : PairCoord (Fin 0)→ℝ := fun _ => 0
    have c : ∀ u : PairCoord (Fin 0)→ℝ, u=x := fun u => Subsingleton.elim _ _
    have e : (gramChart x)=1 := by
      ext i
      exact Fin.elim0 i
    have p : (gramChart x).PosDef := by rw [e]; exact Matrix.PosDef.one
    have w : chartWeight 0 m x=1 := by
      rw [chartWeight_at_pd _ _ _ p,e]
      simp
    simp_rw [c]
    simp [w, Measure.volume_pi_eq_dirac x]
  | succ k ih =>
    have dims : Module.finrank ℝ E=k+m+2 := by omega
    obtain ⟨C,C0,Ct,IH⟩ := ih (m+1) (by omega)
    obtain ⟨Z0,Zt⟩ := projectionMass_nonzero_finite k m
    let Z := projectionMass k m
    refine ⟨C*(Z⁻¹),mul_ne_zero C0 (ENNReal.inv_ne_zero.mpr Zt),
      ENNReal.mul_ne_top Ct (ENNReal.inv_ne_top.mpr Z0),?_⟩
    intro f fm
    let G : (PairCoord (Fin k)→ℝ)→ℝ≥0∞ := gramFiber k m f
    have gm : Measurable G := gramFiber_measurable k m f fm
    let Q : (PairCoord (Fin k)→ℝ)→ℝ≥0∞ := fun u => (G u/Z)/chartWeight k (m+1) u
    have qm : Measurable Q := (gm.div_const _).div (chartWeight_measurable _ _)
    let F : ((Fin k→UnitSphere E)×UnitSphere E)→ℝ≥0∞ :=
      fun v => f (sampleChart ((splitLast k).symm v))
    have Fm : Measurable F := (fm.comp sampleChart_measurable).comp (splitLast k).symm.measurable
    have P := (splitLast_volume μ k).symm (splitLast k)
    have lin := P.lintegral_comp (fm.comp sampleChart_measurable)
    change (∫⁻ v, F v ∂((Measure.pi fun _ : Fin k => μ).prod μ)) =
      (∫⁻ v : Fin (k+1)→UnitSphere E, f (sampleChart v) ∂(Measure.pi fun _ : Fin (k+1) => uniformSphere (volume : Measure E))) at lin
    rw [← lin,lintegral_prod F Fm.aemeasurable]
    have point : ∀ᵐ (v : Fin k→UnitSphere E) ∂(Measure.pi fun _ : Fin k => μ),
        (∫⁻ x : UnitSphere E, F (v,x) ∂μ)=Q (sampleChart v) := by
      filter_upwards [sphere_iid_ae_independent (E:=E) k (by omega)] with v vi
      simp_rw [F,splitLast_symm_apply]
      have law := chart_conditional_weight k m dims v vi f fm
      dsimp only at law
      have pp : (gramChart (sampleChart v)).PosDef := by
        rw [sampleChart_matrix]
        exact Matrix.posDef_gram_of_linearIndependent vi
      have w0 := (chartWeight_positive k (m+1) _ pp).ne'
      have wt := chartWeight_finite k (m+1) (sampleChart v)
      change chartWeight k (m+1) (sampleChart v)*_ = G (sampleChart v)/Z at law
      unfold Q
      rw [← law, mul_comm (chartWeight k (m+1) (sampleChart v)),
        ENNReal.mul_div_cancel_right w0 wt]
    rw [lintegral_congr_ae point,IH Q qm]
    have qeq (u : PairCoord (Fin k)→ℝ) : chartWeight k (m+1) u*Q u=G u/Z := by
      by_cases pd : (gramChart u).PosDef
      · unfold Q
        rw [mul_comm,ENNReal.div_mul_cancel (chartWeight_positive k (m+1) u pd).ne'
          (chartWeight_finite k (m+1) u)]
      · have z : G u=0 := gramFiber_off_support k m f u pd
        simp [Q,z]
    simp_rw [qeq]
    simp_rw [div_eq_mul_inv, mul_comm _ (Z⁻¹)]
    rw [lintegral_const_mul _ gm, ← mul_assoc,gramFiber_integrate k m f fm]
    ac_rfl

#print axioms spherical_joint_gram_weighted
end RobustFolkman.GeometricGap
