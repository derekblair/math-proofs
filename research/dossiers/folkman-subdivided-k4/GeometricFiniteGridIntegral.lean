import GeometricGridEnergyLift

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped BigOperators ENNReal
variable {S I : Type*} [MeasurableSpace S] [Fintype I] [DecidableEq I]

theorem integral_finite_code (μ : Measure S) [IsFiniteMeasure μ]
    (code : S → I) (mc : ∀ i, MeasurableSet (code ⁻¹' {i})) (a : I → ℝ) :
    (∫ x, a (code x) ∂μ)=∑ i, μ.real (code ⁻¹' {i})*a i := by
  have h (x : S) : a (code x)=∑ i : I, (code ⁻¹' {i}).indicator (fun _ => a i) x := by
    rw [Finset.sum_eq_single (code x)]
    · simp [indicator_of_mem]
    · intro b _ hb
      rw [indicator_of_notMem (by simpa [ne_comm] using hb : x ∉ code ⁻¹' {b})]
    · simp
  simp_rw [h]
  rw [integral_finsetSum]
  · congr 1
    ext i
    rw [integral_indicator (mc i), integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
    rfl
  · intro i _
    exact (integrable_const _).indicator (mc i)

theorem integrable_finite_code (μ : Measure S) [IsFiniteMeasure μ]
    (code : S → I) (mc : ∀ i, MeasurableSet (code ⁻¹' {i})) (a : I → ℝ) :
    Integrable (fun x => a (code x)) μ := by
  have h (x : S) : a (code x)=∑ i : I, (code ⁻¹' {i}).indicator (fun _ => a i) x := by
    rw [Finset.sum_eq_single (code x)]
    · simp [indicator_of_mem]
    · intro b _ hb
      rw [indicator_of_notMem (by simpa [ne_comm] using hb : x ∉ code ⁻¹' {b})]
    · simp
  simp_rw [h]
  exact integrable_finsetSum _ (fun i _ => (integrable_const _).indicator (mc i))

/-- Exact finite-grid quadratic expression for the compressed kernel. -/
theorem grid_double_integral (μ : Measure S) [IsProbabilityMeasure μ]
    (code : S → I) (mc : ∀ i, MeasurableSet (code ⁻¹' {i}))
    (K : I→I→ℝ) (v : I → ℝ) :
    let p := fun i => μ.real (code ⁻¹' {i})
    let g := fun x => v (code x) / Real.sqrt (p (code x))
    (∫ x, (∫ y, K (code x) (code y)*(g x*g y) ∂μ) ∂μ)
      = ∑ i, ∑ j, Real.sqrt (p i)*Real.sqrt (p j)*K i j*(v i*v j) := by
  intro p g
  let w := fun i => v i/Real.sqrt (p i)
  change (∫ x, (∫ y, K (code x) (code y)*(w (code x)*w (code y)) ∂μ) ∂μ)=_
  simp_rw [show ∀ x : S, (∫ y, K (code x) (code y)*(w (code x)*w (code y)) ∂μ)=
    ∑ j, p j*(K (code x) j*(w (code x)*w j)) from fun x =>
    integral_finite_code μ code mc (fun j => K (code x) j*(w (code x)*w j))]
  rw [integral_finite_code μ code mc (fun i => ∑ j, p j*(K i j*(w i*w j)))]
  apply Finset.sum_congr rfl
  intro i _
  change p i*(∑ j, p j*(K i j*(w i*w j))) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h (k : I) : p k*w k=Real.sqrt (p k)*v k := by
    have hn : 0≤p k := ENNReal.toReal_nonneg
    rcases eq_or_lt_of_le hn with e|e
    · simp [w,←e]
    · unfold w
      field_simp [ne_of_gt (Real.sqrt_pos.2 e)]
      rw [Real.sq_sqrt hn]
      ring
  calc
    _ = (p i*w i)*(p j*w j)*K i j := by ring
    _ = _ := by rw [h,h]; ring

#print axioms grid_double_integral
end RobustFolkman.GeometricGap
