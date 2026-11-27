import GeometricCapKernel

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped InnerProductSpace ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem capAverage_measurable (t : ℝ) (a : UnitSphere E)
    (f : UnitSphere E→ℝ) (fm : Measurable f) : Measurable (capAverage t f) := by
  let σ := uniformSphere (volume : Measure E)
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  let H := fun p : UnitSphere E×UnitSphere E => capKernel t p.1 p.2*f p.2
  have HM : Measurable H := (capKernel_joint_measurable t).mul (fm.comp measurable_snd)
  have Z : ∀ x, capAverage t f x=(σ.real (capPoints t a))⁻¹*(∫ y, H (x,y) ∂σ) :=
    fun x => capAverage_as_kernel t f a x
  rw [funext Z]
  exact measurable_const.mul HM.stronglyMeasurable.integral_prod_right'.measurable

theorem capAverage_bound (t : ℝ) (t0 : -1<t) (t1 : t<1)
    (f : UnitSphere E→ℝ) (B : ℝ) (bd : ∀ x, ‖f x‖≤B) (x : UnitSphere E) :
    ‖capAverage t f x‖≤B := by
  let τ := capLaw t x
  letI : IsProbabilityMeasure τ := capLaw_probability t t0 t1 x
  have h := norm_integral_le_of_norm_le_const (μ:=τ) (ae_of_all _ bd)
  simpa [Measure.real,capAverage,τ] using h

theorem capAverage_const (t : ℝ) (t0 : -1<t) (t1 : t<1) (a : UnitSphere E) (c : ℝ) :
    capAverage t (fun _ => c) a=c := by
  letI : IsProbabilityMeasure (capLaw t a) := capLaw_probability t t0 t1 a
  simp [capAverage,Measure.real]

theorem capAverage_stationary_bounded (t : ℝ) (t0 : -1<t) (t1 : t<1) (a : UnitSphere E)
    (f : UnitSphere E→ℝ) (fm : Measurable f) (B : ℝ) (B0 : 0≤B) (bd : ∀ x, ‖f x‖≤B) :
    let σ := uniformSphere (volume : Measure E)
    (∫ x,capAverage t f x ∂σ)=∫ x,f x ∂σ := by
  intro σ
  have h := capAverage_symmetry_bounded t a (fun _ => (1:ℝ)) f measurable_const fm 1 B
    (by norm_num) B0 (fun _ => by norm_num) bd
  simpa only [one_mul,capAverage_const t t0 t1 _ 1] using h

theorem bounded_square_integrable {S : Type*} [MeasurableSpace S]
    (f : S→ℝ) (fm : Measurable f) (B : ℝ) (B0 : 0≤B) (bd : ∀ x, ‖f x‖≤B)
    (μ : Measure S) [IsFiniteMeasure μ] :
    Integrable (fun z => (f z)^2) μ := by
  apply Integrable.of_bound (fm.pow_const 2).aestronglyMeasurable (B^2)
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have u := pow_le_pow_left₀ (norm_nonneg _) (bd x) 2
  rwa [Real.norm_eq_abs,sq_abs] at u

theorem capAverage_square_pointwise (t : ℝ) (t0 : -1<t) (t1 : t<1)
    (f : UnitSphere E→ℝ) (fm : Measurable f) (B : ℝ) (B0 : 0≤B) (bd : ∀ x, ‖f x‖≤B)
    (a : UnitSphere E) : (capAverage t f a)^2≤capAverage t (fun z => (f z)^2) a := by
  let μ := capLaw t a
  letI : IsProbabilityMeasure μ := capLaw_probability t t0 t1 a
  exact integral_sq_lower μ f (Integrable.of_bound fm.aestronglyMeasurable B (ae_of_all _ bd))
    (bounded_square_integrable f fm B B0 bd μ)

/-- The exact cap transition is stationary and contractive in L² for
every bounded measurable test, with no kernel approximation. -/
theorem capAverage_l2_bounded (t : ℝ) (t0 : -1<t) (t1 : t<1) (a : UnitSphere E)
    (f : UnitSphere E→ℝ) (fm : Measurable f) (B : ℝ) (B0 : 0≤B) (bd : ∀ x, ‖f x‖≤B) :
    let σ := uniformSphere (volume : Measure E)
    (∫ z, (capAverage t f z)^2 ∂σ)≤∫ z, (f z)^2 ∂σ := by
  intro σ
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  let g := fun z => (f z)^2
  have gm : Measurable g := fm.pow_const 2
  have gb : ∀ x, ‖g x‖≤B^2 := by
    intro x
    change ‖(f x)^2‖≤B^2
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (bd x) 2
  have h := capAverage_stationary_bounded t t0 t1 a g gm (B^2) (sq_nonneg _) gb
  change _ = ∫ z, (f z)^2 ∂σ at h
  rw [←h]
  have fi := bounded_square_integrable _ (capAverage_measurable t a f fm) B B0
    (capAverage_bound t t0 t1 f B bd) σ
  have gi := Integrable.of_bound (capAverage_measurable t a g gm).aestronglyMeasurable (B^2)
    (ae_of_all σ (capAverage_bound t t0 t1 g (B^2) gb))
  exact integral_mono fi gi (capAverage_square_pointwise t t0 t1 f fm B B0 bd)

#print axioms capAverage_l2_bounded
end RobustFolkman.GeometricGap
