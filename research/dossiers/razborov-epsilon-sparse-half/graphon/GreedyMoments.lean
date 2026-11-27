import GreedyAveraging

open Set MeasureTheory Function
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X] (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]

noncomputable def rootCross (K : Kernel X) (D : X→ℝ) (v : X) :=
  load μ K (D*deg ν K) v

/-- Fubini identifies the averaged anchor-to-neighborhood cross
energy as the second moment of the capped marked degree. -/
theorem greedy_cross_moment (K : Kernel X) (D : X→ℝ) (hD : BMeas D)
    (hD0 : ∀ x, 0≤D x) (a b c : ℝ)
    (hd : (∫ x,D x ∂μ)=1-a-b)
    (hc : (∫ x,D x*deg ν K x ∂μ)=c/2)
    (hdeg : ∀ x, 0<D x → 1/2-a≤deg ν K x ∧ deg ν K x≤b/2) :
    (∫ v,rootCross μ ν K D v ∂ν) ≤ (1/2-a+b/2)*c/2-(b/2)*(1/2-a)*(1-a-b) := by
  have hb := deg_bmeas ν K
  unfold rootCross
  rw [load_marginal μ ν K (D*deg ν K) (hD.mul hb)]
  let hi := b/2
  let lo := 1/2-a
  have i₁ : Integrable (fun x=>D x*deg ν K x*deg ν K x) μ :=
    bMeas_integrable μ ((hD.mul hb).mul hb)
  have i₂ : Integrable (fun x=>(lo+hi)*(D x*deg ν K x)-hi*lo*D x) μ :=
    ((bMeas_integrable μ (hD.mul hb)).const_mul (lo+hi)).sub
      ((bMeas_integrable μ hD).const_mul (hi*lo))
  have hh := integral_mono i₁ i₂ (fun x=>by
    by_cases hz : D x=0
    · simp [hz]
    · obtain ⟨h₁,h₂⟩ := hdeg x (lt_of_le_of_ne (hD0 x) (Ne.symm hz))
      have h := mul_nonneg (mul_nonneg (hD0 x)
        (show 0≤deg ν K x-lo from sub_nonneg.mpr h₁))
        (show 0≤hi-deg ν K x from sub_nonneg.mpr h₂)
      nlinarith only [h])
  have iL : Integrable (fun x=>(lo+hi)*(D x*deg ν K x)) μ :=
    (bMeas_integrable μ (hD.mul hb)).const_mul _
  have iR : Integrable (fun x=>hi*lo*D x) μ := (bMeas_integrable μ hD).const_mul _
  rw [integral_sub iL iR,integral_const_mul,integral_const_mul,hc,hd] at hh
  change _ ≤ (lo+hi)*(c/2)-hi*lo*(1-a-b) at hh
  convert hh using 1
  ring

#print axioms greedy_cross_moment
end SparseHalfGraphon
