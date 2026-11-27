import GeometricCapHeightTail

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped InnerProductSpace ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem conditional_cap_height_second (n : ℕ) (dim : Module.finrank ℝ E=n+3)
    (t : ℝ) (tp : 0<t) (ts : t≤1/8) (large : 3≤(n:ℝ)/2)
    (dense : 1≤4*((n:ℝ)/2)*t^2) (a : UnitSphere E) :
    (∫ z : UnitSphere E, (⟪a.val,z.val⟫_ℝ)^2
     ∂condOn (uniformSphere (volume : Measure E)) (capPoints t a)) ≤
      4*t^2+Real.exp (3-2*((n:ℝ)/2)*t^2) := by
  let σ := uniformSphere (volume : Measure E)
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  let P := capPoints t a
  let Q := capPoints (2*t) a
  let τ := condOn σ P
  have p0 : σ P≠0 := (capPoints_both_positive t (by linarith only [tp])
    (by linarith only [ts]) a).1.ne'
  letI : IsProbabilityMeasure τ := condOn_probability σ _ p0 (measure_ne_top σ P)
  have pm : MeasurableSet P := capPoints_measurable t a
  have qm : MeasurableSet Q := capPoints_measurable (2*t) a
  have sub : Q⊆P := fun z hz => (show t≤2*t by linarith only [tp]).trans hz
  let C := Real.exp (3-2*((n:ℝ)/2)*t^2)
  have C0 : 0≤C := (Real.exp_pos _).le
  have tail := cap_double_height_tail n dim t tp ts large dense a
  have law : τ Q≤ENNReal.ofReal C := by
    unfold τ condOn
    rw [Measure.smul_apply,smul_eq_mul,Measure.restrict_apply qm,inter_eq_left.mpr sub]
    calc
      _ ≤ (σ P)⁻¹*(ENNReal.ofReal C*σ P) := by gcongr
      _ = (ENNReal.ofReal C)*((σ P)⁻¹*σ P) := by ac_rfl
      _ = _ := by rw [ENNReal.inv_mul_cancel p0 (measure_ne_top σ P),mul_one]
  have tailR : τ.real Q≤C := by
    unfold Measure.real
    simpa only [ENNReal.toReal_ofReal C0] using
      (ENNReal.toReal_mono ENNReal.ofReal_ne_top law)
  let f := fun z : UnitSphere E => (⟪a.val,z.val⟫_ℝ)^2
  let q := Q.indicator (fun _ => (1:ℝ))
  have fI : Integrable f τ := sphere_inner_square_integrable a τ
  have qI : Integrable q τ := (integrable_const _).indicator qm
  have support : ∀ᵐ z ∂τ, z∈P := by
    rw [ae_iff]
    change τ Pᶜ=0
    unfold τ condOn
    rw [Measure.smul_apply,smul_eq_mul,Measure.restrict_apply pm.compl,
      compl_inter_self,measure_empty,mul_zero]
  have m : (∫ z, f z ∂τ)≤∫ z, (4*t^2+q z) ∂τ := by
    apply integral_mono_ae fI ((integrable_const _).add qI)
    filter_upwards [support] with z hz
    by_cases h : z∈Q
    · have v := abs_real_inner_le_norm a.val z.val
      rw [show ‖a.val‖=1 by simpa using a.property,show ‖z.val‖=1 by simpa using z.property,
        mul_one] at v
      have g := pow_le_pow_left₀ (abs_nonneg _) v 2
      rw [sq_abs,one_pow] at g
      change (⟪a.val,z.val⟫_ℝ)^2≤4*t^2+q z
      simp only [q,indicator_of_mem h]
      nlinarith only [g,sq_nonneg t]
    · have h0 : 0≤⟪a.val,z.val⟫_ℝ := tp.le.trans hz
      have ht : ⟪a.val,z.val⟫_ℝ≤2*t := (lt_of_not_ge h).le
      have s := pow_le_pow_left₀ h0 ht 2
      change (⟪a.val,z.val⟫_ℝ)^2≤4*t^2+q z
      simp only [q,indicator_of_notMem h,add_zero]
      nlinarith only [s]
  rw [integral_add (integrable_const _) qI,integral_const,
    show τ.real univ=1 by simp [Measure.real],one_smul] at m
  have qi : (∫ z, q z ∂τ)=τ.real Q := by
    unfold q
    rw [integral_indicator qm,MeasureTheory.setIntegral_const]
    simp
  rw [qi] at m
  exact m.trans (by linarith only [tailR])

#print axioms conditional_cap_height_second
end RobustFolkman.GeometricGap
