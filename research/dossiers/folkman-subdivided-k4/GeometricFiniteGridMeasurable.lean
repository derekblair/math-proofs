import GeometricFiniteGridIntegral

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped BigOperators ENNReal
variable {S I : Type*} [MeasurableSpace S] [Fintype I]

theorem measurable_finite_code (code : S → I) (mc : ∀ i, MeasurableSet (code ⁻¹' {i}))
    (a : I→ℝ) : Measurable (fun x => a (code x)) := by
  classical
  have h (x : S) : a (code x)=∑ i : I, (code ⁻¹' {i}).indicator (fun _ => a i) x := by
    rw [Finset.sum_eq_single (code x)]
    · simp [indicator_of_mem]
    · intro b _ hb
      rw [indicator_of_notMem (by simpa [ne_comm] using hb : x ∉ code ⁻¹' {b})]
    · simp
  simp_rw [h]
  exact Finset.measurable_sum _ (fun i _ => measurable_const.indicator (mc i))

theorem finite_code_bound (code : S → I) (a : I→ℝ) (x : S) :
    ‖a (code x)‖ ≤ ∑ i, ‖a i‖ :=
  Finset.single_le_sum (fun i _ => norm_nonneg (a i)) (Finset.mem_univ (code x))

theorem measurable_pair_code (code : S→I) (mc : ∀ i, MeasurableSet (code ⁻¹' {i}))
    (K : I→I→ℝ) : Measurable (fun z : S×S => K (code z.1) (code z.2)) := by
  classical
  let c := fun z : S×S => (code z.1,code z.2)
  have h (i : I×I) : c ⁻¹' {i} = (code ⁻¹' {i.1}) ×ˢ (code ⁻¹' {i.2}) := by
    ext z
    simp [c,Prod.ext_iff]
  exact measurable_finite_code c (fun i => by
    rw [h i]
    exact (mc i.1).prod (mc i.2)) (fun i => K i.1 i.2)

#print axioms measurable_pair_code
end RobustFolkman.GeometricGap
