import StepHalves

open Set MeasureTheory SparseHalfGraphon
open scoped ENNReal
namespace SparseHalfCountableEndpoint
variable {X : Type*} [MeasurableSpace X]
variable {I : Type*} [Fintype I]
variable (P : I→Set X) (e : I→I→Bool)
variable (μ : Measure X) [IsFiniteMeasure μ]

/-- A.e. zero on every forbidden rectangle is exactly the domination
needed for completion, provided the bank covers almost every point. -/
theorem dominated_step (B : Cells P) (sym : ∀ i j,e i j=e j i)
    (K : Kernel X) (cover : ∀ᵐ x ∂μ, ∃ i,x∈P i)
    (zeros : ∀ i j,e i j=false →
      ∀ᵐ z ∂(μ.restrict (P i)).prod (μ.restrict (P j)),K.W z=0) :
    ∀ᵐ z ∂μ.prod μ, K.W z≤(stepKernel P e B sym).W z := by
  have Z (i j : I) : ∀ᵐ z ∂μ.prod μ, e i j=false → z.1∈P i → z.2∈P j → K.W z=0 := by
    by_cases ht : e i j=false
    · have h := zeros i j ht
      rw [Measure.prod_restrict,ae_restrict_iff' ((B.meas i).prod (B.meas j))] at h
      exact h.mono fun z hz _ h₁ h₂ => hz ⟨h₁,h₂⟩
    · exact ae_of_all _ (fun _ he => (ht he).elim)
  have both := ae_all_iff.2 (fun i => ae_all_iff.2 (Z i))
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ:=μ) (ν:=μ)).ae cover,(Measure.quasiMeasurePreserving_snd (μ:=μ) (ν:=μ)).ae cover,both] with ⟨x,y⟩ ⟨i,hi⟩ ⟨j,hj⟩ hz
  change K.W (x,y)≤ stepW P e (x,y)
  rw [stepW_on P e B i j hi hj]
  cases he : e i j
  · rw [hz i j he hi hj]; exact le_rfl
  · exact K.le_one _

/-- Exact finite formula for the cost of a constant-on-cell half. -/
theorem step_energy (B : Cells P) (sym : ∀ i j,e i j=e j i)
    (q : I→ℝ) (hq : ∀ i,0≤q i ∧ q i≤μ.real (P i)) (mass : ∑ i,q i=1/2) :
    halfEnergy μ (stepKernel P e B sym) (stepHalf P μ B q hq mass) =
      (∑ a : I×I, q a.1*q a.2*(if e a.1 a.2 then 1 else 0))/2 := by
  let f := stepAllocation P μ q
  let ρ := reweight μ f
  let H := stepHalf P μ B q hq mass
  haveI : IsFiniteMeasure ρ := isFiniteMeasure_of_le μ (reweight_le μ f H.le_one)
  have masses (i : I) : ρ.real (P i)=q i := by
    have eq (x : X) : (P i).indicator (fun _ => (1:ℝ)) x * f x = allocSet μ (P i) (q i) x := by
      by_cases hx : x∈P i
      · rw [indicator_of_mem hx,one_mul,show f x=q i/μ.real (P i) from stepAllocation_on P μ B q hx]
        exact (indicator_of_mem hx (fun _ => q i/μ.real (P i))).symm
      · rw [indicator_of_notMem hx (fun _ => (1:ℝ)),zero_mul,allocSet_support μ (P i) (q i) hx]
    have z := reweight_integral μ f H.measurable_f H.nn ((P i).indicator (fun _ => (1:ℝ)))
    change (∫ x,(P i).indicator (fun _ => (1:ℝ)) x ∂ρ) = _ at z
    rw [integral_indicator (B.meas i),setIntegral_const,smul_eq_mul,mul_one] at z
    rw [z]
    simp_rw [mul_comm (f _),eq]
    exact allocSet_mass μ (P i) (B.meas i) (q i) (hq i).1 (hq i).2
  have ints (a : I×I) : Integrable
      ((P a.1 ×ˢ P a.2).indicator (fun _ : X×X => if e a.1 a.2 then (1:ℝ) else 0)) (ρ.prod ρ) :=
    (integrable_const _).indicator ((B.meas a.1).prod (B.meas a.2))
  rw [halfEnergy_as_pair]
  change energyPair μ (stepKernel P e B sym) f f / 2=_
  rw [←reweight_energy μ (stepKernel P e B sym) f f H.measurable_f H.measurable_f H.nn H.nn H.le_one H.le_one]
  change (∫ z,stepW P e z ∂ρ.prod ρ)/2=_
  unfold stepW
  rw [integral_finsetSum _ (fun a _ => ints a)]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_indicator ((B.meas a.1).prod (B.meas a.2)),setIntegral_const,smul_eq_mul]
  have he : (ρ.prod ρ).real (P a.1 ×ˢ P a.2) = ρ.real (P a.1)*ρ.real (P a.2) := by
    unfold Measure.real
    rw [Measure.prod_prod,ENNReal.toReal_mul]
  rw [he,masses,masses]

#print axioms dominated_step
#print axioms step_energy
end SparseHalfCountableEndpoint
