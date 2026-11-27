import GeometricCenteredEnergy

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped BigOperators ENNReal
variable {S I : Type*} [MeasurableSpace S] [Fintype I] [DecidableEq I]

/-- Lifting a finite test vector through a measurable partition does not
increase its energy, including when a cell has probability zero. -/
theorem grid_energy_lift (μ : Measure S) [IsProbabilityMeasure μ]
    (code : S → I) (mc : ∀ i, MeasurableSet (code ⁻¹' {i}))
    (v : I → ℝ) :
    let p := fun i => μ.real (code ⁻¹' {i})
    let g := fun x => v (code x) / Real.sqrt (p (code x))
    energyNorm μ g ≤ Real.sqrt (∑ i, (v i)^2) := by
  classical
  intro p g
  let w := fun i => v i / Real.sqrt (p i)
  have fg (x : S) : (g x)^2 = ∑ i : I, (code ⁻¹' {i}).indicator (fun _ => (w i)^2) x := by
    rw [Finset.sum_eq_single (code x)]
    · simp [g,w,indicator_of_mem]
    · intro b _ hb
      rw [indicator_of_notMem (by simpa [ne_comm] using hb : x ∉ code ⁻¹' {b})]
    · simp
  unfold energyNorm
  apply Real.sqrt_le_sqrt
  simp_rw [fg]
  rw [integral_finsetSum]
  · apply Finset.sum_le_sum
    intro i _
    rw [integral_indicator (mc i), integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
    change p i*(v i / Real.sqrt (p i))^2≤(v i)^2
    have pn : 0 ≤ p i := ENNReal.toReal_nonneg
    rcases eq_or_lt_of_le pn with h|h
    · rw [←h,zero_mul]
      positivity
    · rw [div_pow, Real.sq_sqrt pn]
      field_simp [ne_of_gt h] <;> rfl
  · intro i _
    exact (integrable_const ((w i)^2)).indicator (mc i)

#print axioms grid_energy_lift
end RobustFolkman.GeometricGap
