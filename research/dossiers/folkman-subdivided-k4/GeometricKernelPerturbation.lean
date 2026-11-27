import GeometricPopulationL2

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped ENNReal
variable {S : Type*} [MeasurableSpace S]

/-- For a bounded kernel changing by at most one on a small exceptional
set, the error of a lifted quadratic test is controlled by its L² energy.
This bound is independent of the maximum height of that test. -/
theorem kernel_quadratic_perturbation (μ : Measure S) [IsProbabilityMeasure μ]
    (e : Set (S×S)) (em : MeasurableSet e)
    (D : S×S→ℝ) (Dm : Measurable D)
    (db : ∀ p, ‖D p‖ ≤ e.indicator (fun _ => 1) p)
    (f : S→ℝ) (fm : Measurable f) (B : ℝ) (bd : ∀ x, ‖f x‖ ≤ B) :
    ‖∫ p, D p*(f p.1*f p.2) ∂(μ.prod μ)‖ ≤
      Real.sqrt ((μ.prod μ).real e) * (energyNorm μ f)^2 := by
  let ν := μ.prod μ
  let χ := e.indicator (fun _ => (1:ℝ))
  let u := fun p : S×S => ‖f p.1 * f p.2‖
  have χm : Measurable χ := measurable_const.indicator em
  have χb (p : S×S) : ‖χ p‖ ≤ 1 := by
    by_cases h : p∈e <;> simp [χ,h]
  have um : Measurable u := ((fm.comp measurable_fst).mul (fm.comp measurable_snd)).norm
  have ub (p : S×S) : ‖u p‖ ≤ B*B := by
    change ‖‖f p.1*f p.2‖‖ ≤ _
    rw [norm_norm,norm_mul]
    exact mul_le_mul (bd p.1) (bd p.2) (norm_nonneg _) ((norm_nonneg _).trans (bd p.1))
  have dI : Integrable (fun p => ‖D p*(f p.1*f p.2)‖) ν := by
    apply Integrable.of_bound (Dm.mul ((fm.comp measurable_fst).mul (fm.comp measurable_snd))).norm.aestronglyMeasurable (B*B)
    apply ae_of_all
    intro p
    change ‖‖D p*(f p.1*f p.2)‖‖ ≤ _
    rw [norm_norm,norm_mul]
    have h : ‖D p‖≤1 := (db p).trans ((le_abs_self (χ p)).trans (χb p))
    exact (mul_le_mul h (by simpa only [u,norm_norm] using ub p) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have rI : Integrable (fun p => χ p*u p) ν := by
    apply Integrable.of_bound (χm.mul um).aestronglyMeasurable (B*B)
    apply ae_of_all
    intro p
    change ‖χ p*u p‖ ≤ _
    rw [norm_mul]
    exact (mul_le_mul (χb p) (ub p) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have cχ : energyNorm ν χ=Real.sqrt (ν.real e) := by
    unfold energyNorm
    have h (p : S×S) : (χ p)^2=χ p := by
      by_cases hp : p∈e <;> simp [χ,hp]
    simp_rw [h]
    unfold χ Measure.real
    rw [integral_indicator em,integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one]
  have cu : energyNorm ν u=(energyNorm μ f)^2 := by
    unfold energyNorm
    have h (p : S×S) : (u p)^2=(f p.1)^2*(f p.2)^2 := by
      simp only [u,Real.norm_eq_abs,sq_abs,mul_pow]
    simp_rw [h]
    change Real.sqrt (∫ p : S×S, (f p.1)^2*(f p.2)^2 ∂(μ.prod μ)) = _
    rw [integral_prod_mul (fun x => (f x)^2) (fun x => (f x)^2), Real.sqrt_mul (by positivity), ←pow_two]
  calc
    _ ≤ ∫ p, ‖D p*(f p.1*f p.2)‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ p, χ p*u p ∂ν := integral_mono dI rI (fun p => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (db p) (norm_nonneg _))
    _ ≤ energyNorm ν χ * energyNorm ν u :=
      energy_cauchy ν χ u (MemLp.of_bound χm.aestronglyMeasurable 1 (ae_of_all _ χb))
        (MemLp.of_bound um.aestronglyMeasurable (B*B) (ae_of_all _ ub))
    _ = _ := by rw [cχ,cu]

#print axioms kernel_quadratic_perturbation
end RobustFolkman.GeometricGap
