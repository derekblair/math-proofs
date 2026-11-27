import GeometricCenteredEnergy

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped InnerProductSpace ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- The raw spherical kernel minus its row mass has a small population
operator bound on all bounded measurable functions, without a mean assumption. -/
theorem centered_cap_energy (n : ℕ) (dim : Module.finrank ℝ E=n+3)
    (t : ℝ) (tp : 0<t) (ts : t≤1/8) (large : 3≤(n:ℝ)/2)
    (dense : 1≤4*((n:ℝ)/2)*t^2) (a : UnitSphere E)
    (f : UnitSphere E→ℝ) (fm : Measurable f) (B : ℝ) (B0 : 0≤B) (bd : ∀ x, ‖f x‖≤B) :
    let σ := uniformSphere (volume : Measure E)
    let q := σ.real (capPoints t a)
    energyNorm σ (fun x => ∫ y, (capKernel t x y-q)*f y ∂σ) ≤
      q*Real.sqrt (squaredCapContraction n t)*energyNorm σ f := by
  intro σ q
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  let m := ∫ y, f y ∂σ
  let g := fun y => f y-m
  have gm : Measurable g := fm.sub measurable_const
  have gb (x) : ‖g x‖≤B+‖m‖ := (norm_sub_le _ _).trans (add_le_add_left (bd x) _)
  have t0 : -1<t := by linarith only [tp]
  have t1 : t<1 := by linarith only [ts]
  have qp : 0<q := ENNReal.toReal_pos (capPoints_both_positive t t0 t1 a).1.ne'
    (measure_ne_top σ _)
  obtain ⟨gz,ge⟩ := centered_energy σ f fm bd
  have con := cap_l2_contraction_bounded n dim t tp ts large dense a g gm
    (B+‖m‖) (by positivity) gb gz
  have fi : Integrable f σ := Integrable.of_bound fm.aestronglyMeasurable B (ae_of_all _ bd)
  have eq (x : UnitSphere E) :
      (∫ y, (capKernel t x y-q)*f y ∂σ)=q*capAverage t g x := by
    have kgm : Measurable (capKernel t x) :=
      (capKernel_joint_measurable t).comp (measurable_const.prodMk measurable_id)
    have ki : Integrable (capKernel t x) σ := Integrable.of_bound
      kgm.aestronglyMeasurable 1 (ae_of_all _ (norm_capKernel_le_one t x))
    have kf : Integrable (fun y => capKernel t x y*f y) σ := by
      apply Integrable.of_bound (kgm.mul fm).aestronglyMeasurable B
      apply ae_of_all
      intro y
      change ‖capKernel t x y*f y‖≤B
      rw [norm_mul]
      exact (mul_le_mul (norm_capKernel_le_one t x y) (bd y) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
    have km : (∫ y, capKernel t x y ∂σ)=q := by
      unfold capKernel
      rw [integral_indicator (capPoints_measurable t x), integral_const,
        Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_one]
      exact congrArg ENNReal.toReal (capPoints_mass_root_constant t x a)
    have ea := capAverage_as_kernel t g a x
    change capAverage t g x=q⁻¹*(∫ y, capKernel t x y*g y ∂σ) at ea
    rw [ea,←mul_assoc,mul_inv_cancel₀ (ne_of_gt qp),one_mul]
    simp_rw [sub_mul,g,mul_sub]
    rw [integral_sub kf (fi.const_mul _),integral_sub kf (ki.mul_const _),
      integral_const_mul,integral_mul_const,km]
  rw [funext eq]
  have scale : energyNorm σ (fun x => q*capAverage t g x)=q*energyNorm σ (capAverage t g) := by
    unfold energyNorm
    simp_rw [mul_pow,integral_const_mul]
    rw [Real.sqrt_mul (sq_nonneg q),Real.sqrt_sq (le_of_lt qp)]
  rw [scale]
  calc
    q*energyNorm σ (capAverage t g) ≤ q*(Real.sqrt (squaredCapContraction n t)*energyNorm σ g) :=
      mul_le_mul_of_nonneg_left con (le_of_lt qp)
    _ = (q*Real.sqrt (squaredCapContraction n t))*energyNorm σ g := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left ge (by positivity)

#print axioms centered_cap_energy
end RobustFolkman.GeometricGap
