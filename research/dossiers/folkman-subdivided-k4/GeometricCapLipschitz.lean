import GeometricCapCoupling

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped InnerProductSpace NNReal

theorem integral_sq_lower {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (f : S→ℝ)
    (fi : Integrable f μ) (f2 : Integrable (fun z => (f z)^2) μ) :
    (∫ z, f z ∂μ)^2≤∫ z, (f z)^2 ∂μ := by
  let m := ∫ z, f z ∂μ
  have h : (0:ℝ)≤∫ z, (f z-m)^2 ∂μ := integral_nonneg fun z => sq_nonneg _
  have e (z : S) : (f z-m)^2=(f z)^2-(2*m)*f z+m^2 := by ring
  simp_rw [e] at h
  have mulI : Integrable (fun z => (2*m)*f z) μ := fi.const_mul _
  have subI : Integrable (fun z => (f z)^2-(2*m)*f z) μ := f2.sub mulI
  rw [integral_add subI (integrable_const _),
    integral_sub f2 mulI,integral_const_mul,integral_const,
    show μ.real univ=1 by simp [Measure.real],one_smul] at h
  change m^2≤_
  nlinarith only [h]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem unit_sphere_dist_le_two (a b : UnitSphere E) : dist a b≤2 := by
  change dist a.val b.val≤2
  rw [dist_eq_norm]
  have x : ‖a.val‖=1 := by simpa using a.property
  have y : ‖b.val‖=1 := by simpa using b.property
  exact (norm_sub_le _ _).trans (by norm_num [x,y])

theorem integrable_lipschitz_sphere (ν : Measure (UnitSphere E)) [IsFiniteMeasure ν]
    (f : UnitSphere E→ℝ) (L : ℝ≥0) (hf : LipschitzWith L f) (base : UnitSphere E) :
    Integrable f ν := by
  refine Integrable.of_bound hf.continuous.measurable.aestronglyMeasurable (2*(L:ℝ)+‖f base‖) ?_
  apply ae_of_all
  intro z
  calc
    _ = ‖(f z-f base)+f base‖ := by ring_nf
    _ ≤ ‖f z-f base‖+‖f base‖ := norm_add_le _ _
    _ ≤ _ := by
      have hh := hf.dist_le_mul z base
      rw [dist_eq_norm] at hh
      have dd := mul_le_mul_of_nonneg_left (unit_sphere_dist_le_two z base) L.coe_nonneg
      linarith only [hh,dd]

noncomputable def capAverage (t : ℝ) (f : UnitSphere E→ℝ) (a : UnitSphere E) : ℝ :=
  ∫ z, f z ∂capLaw t a

/-- The cap transition contracts Lipschitz seminorm by a factor that can
be made arbitrarily small by fixing a small threshold and increasing
dimension. This does not yet identify the operator on L². -/
theorem cap_average_pointwise_lipschitz (n : ℕ) (dim : Module.finrank ℝ E=n+3)
    (t : ℝ) (tp : 0<t) (ts : t≤1/8) (large : 3≤(n:ℝ)/2)
    (dense : 1≤4*((n:ℝ)/2)*t^2) (f : UnitSphere E→ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) (a b : UnitSphere E) :
    dist (capAverage t f a) (capAverage t f b)≤
      ((L:ℝ)*Real.sqrt (squaredCapContraction n t))*dist a b := by
  obtain ⟨R,hR,bd⟩ := cap_coupling_squared_bound n dim t tp ts large dense a b
  let μ := capLaw t a
  let ν := capLaw t b
  letI : IsProbabilityMeasure μ := capLaw_probability t (by linarith only [tp]) (by linarith only [ts]) a
  letI : IsProbabilityMeasure ν := capLaw_probability t (by linarith only [tp]) (by linarith only [ts]) b
  let D := fun z : UnitSphere E => ‖R z.val-z.val‖
  have D0 (z) : 0≤D z := norm_nonneg _
  have dm : Measurable D := by unfold D; fun_prop
  have d2 (z : UnitSphere E) : D z≤2 := by
    have q := unit_sphere_dist_le_two (sphereRotation R z) z
    change dist (R z.val) z.val≤2 at q
    rw [dist_eq_norm] at q
    exact q
  have di : Integrable D μ := by
    apply Integrable.of_bound dm.aestronglyMeasurable 2
    exact ae_of_all _ fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (D0 z)]; exact d2 z
  have di2 : Integrable (fun z => (D z)^2) μ := by
    apply Integrable.of_bound (dm.pow_const 2).aestronglyMeasurable 4
    apply ae_of_all
    intro z
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    simpa only [show (2:ℝ)^2=4 by norm_num] using pow_le_pow_left₀ (D0 z) (d2 z) 2
  have dr : (∫ z,D z ∂μ)≤Real.sqrt (squaredCapContraction n t)*dist a b := by
    have q := integral_sq_lower μ D di di2
    have p : 0≤squaredCapContraction n t := by unfold squaredCapContraction; positivity
    apply (sq_le_sq₀ (integral_nonneg D0) (by positivity)).1
    rw [mul_pow,Real.sq_sqrt p]
    apply q.trans
    have d : dist a b=‖b.val-a.val‖ := by
      change dist a.val b.val=_
      rw [dist_eq_norm,norm_sub_rev]
    rw [d,mul_comm]
    exact bd
  have fI := integrable_lipschitz_sphere μ f L hf a
  have gI : Integrable (fun z => f (sphereRotation R z)) μ :=
    hR.integrable_comp_of_integrable (integrable_lipschitz_sphere ν f L hf b)
  have u : (∫ z, f (sphereRotation R z) ∂μ) = ∫ z, f z ∂ν :=
    hR.integral_comp' f
  change ‖(∫ z, f z ∂μ)-(∫ z, f z ∂ν)‖≤_
  rw [←u,←integral_sub fI gI]
  refine (norm_integral_le_integral_norm _).trans ?_
  have qi : Integrable (fun z => (L:ℝ)*D z) μ := di.const_mul _
  have q : ∫ z, ‖f z - f (sphereRotation R z)‖ ∂μ ≤ ∫ z, (L:ℝ)*D z ∂μ := by
    apply integral_mono (fI.sub gI).norm qi
    intro z
    have h := hf.dist_le_mul z (sphereRotation R z)
    change dist (f z) (f (sphereRotation R z))≤(L:ℝ)*dist z.val (R z.val) at h
    rw [dist_eq_norm,dist_eq_norm,norm_sub_rev z.val (R z.val)] at h
    exact h
  rw [integral_const_mul] at q
  exact q.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left dr L.coe_nonneg)

#print axioms cap_average_pointwise_lipschitz
end RobustFolkman.GeometricGap
