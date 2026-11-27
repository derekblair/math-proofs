import GeometricSpectralInterface

namespace RobustFolkman.GeometricGap
open MeasureTheory Set Finset
open scoped ENNReal
variable {S I : Type*} [MeasurableSpace S] [Fintype I]

noncomputable def condOn (σ : Measure S) (A : Set S) : Measure S :=
  (σ A)⁻¹ • σ.restrict A

theorem condOn_probability (σ : Measure S) (A : Set S)
    (nz : σ A≠0) (nt : σ A≠∞) : IsProbabilityMeasure (condOn σ A) := by
  constructor
  rw [condOn,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul,
    ENNReal.inv_mul_cancel nz nt]

theorem unnormalize_condOn (σ : Measure S) (A : Set S) (nz : σ A≠0) (nt : σ A≠∞) :
    σ A • condOn σ A = σ.restrict A := by
  rw [condOn,smul_smul,ENNReal.mul_inv_cancel nz nt,one_smul]

theorem conditional_product (σ : Measure S) [IsProbabilityMeasure σ] (A : I→Set S)
    (nz : ∀ i, σ (A i)≠0) :
    (Measure.pi (fun _ : I => σ)).restrict (Set.univ.pi A) =
      (∏ i, σ (A i)) • Measure.pi (fun i : I => condOn σ (A i)) := by
  classical
  letI (i : I) : IsProbabilityMeasure (condOn σ (A i)) :=
    condOn_probability σ _ (nz i) (measure_ne_top σ _)
  rw [Measure.restrict_pi_pi]
  apply Measure.pi_eq
  intro parts _
  rw [Measure.smul_apply,smul_eq_mul,Measure.pi_pi,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← smul_eq_mul,← Measure.smul_apply,unnormalize_condOn σ (A i) (nz i) (measure_ne_top σ _)]

/-- Selecting exactly the coordinates whose samples are in a set A does
not induce dependence among the retained samples. This is the normalized
measure identity underlying every fixed-root cap neighborhood. -/
theorem bernoulli_label_conditioning (σ : Measure S) [IsProbabilityMeasure σ] (A : Set S)
    (a0 : σ A≠0) (a1 : σ Aᶜ≠0) (L : Finset I) [DecidableEq I] :
    let slices := fun i => if i∈L then A else Aᶜ
    (Measure.pi (fun _ : I => σ)).restrict (Set.univ.pi slices) =
      (∏ i, σ (slices i)) • Measure.pi (fun i => condOn σ (slices i)) := by
  intro slices
  apply conditional_product
  intro i
  dsimp [slices]
  split <;> assumption

#print axioms bernoulli_label_conditioning
end RobustFolkman.GeometricGap
