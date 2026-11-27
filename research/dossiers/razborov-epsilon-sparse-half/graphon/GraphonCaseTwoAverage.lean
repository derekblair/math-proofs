import KernelPullback

open MeasureTheory Set
namespace SparseHalfGraphon
variable {X : Type*} [MeasurableSpace X]
variable (ν : Measure X) [IsFiniteMeasure ν]

lemma BMeas.sq {h : X→ℝ} (hh : BMeas h) : BMeas (fun x => h x^2) := by
  obtain ⟨hm,C,hC⟩ := hh
  refine ⟨hm.pow_const 2,C^2,fun x => ?_⟩
  change |(h x)^2|≤C^2
  calc
    |(h x)^2|=(|h x|)^2 := by rw [abs_of_nonneg (sq_nonneg _),sq_abs]
    _ ≤ C^2 := pow_le_pow_left₀ (abs_nonneg _) (hC x) 2

lemma integral_sq_pos {h : X→ℝ} (hh : BMeas h)
    (hp : 0<∫ x, h x ∂ν) : 0<∫ x, h x^2 ∂ν := by
  have hi := bMeas_integrable ν hh.sq
  have h0 : 0≤∫ x, h x^2 ∂ν := integral_nonneg (fun _ => sq_nonneg _)
  by_contra! hn
  have hz : (∫ x, h x^2 ∂ν)=0 := le_antisymm hn h0
  have hsq := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (h x)) hi).mp hz
  have hh0 : h =ᵐ[ν] 0 := by
    filter_upwards [hsq] with x hx
    have he : h x*h x=0 := by change h x^2=0 at hx; simpa only [← pow_two] using hx
    exact (mul_eq_zero.mp he).elim id id
  rw [integral_congr_ae hh0] at hp
  change 0<(∫ _ : X, (0:ℝ) ∂ν) at hp
  rw [integral_zero] at hp
  exact lt_irrefl _ hp

/-- Strict averaging for the Case 2 certificate, after the exact Fubini
marginal identities provide the two deficit bounds. -/
theorem case_two_average (β Z : ℝ) (h r : X→ℝ)
    (hν : mass ν=2/5) (hh : BMeas h) (hr : BMeas r)
    (hZ : 0<Z) (hhs : (∫ x, h x ∂ν)=Z) (hrs : Z/10≤∫ x, r x ∂ν)
    (hloc : ∀ᵐ x ∂ν, β-1/50≤h x/10-(3/4)*h x^2-r x) :
    β<1/50 := by
  have hp : 0<∫ x, h x ∂ν := hhs ▸ hZ
  have hpos := integral_sq_pos ν hh hp
  have h₁ : Integrable (fun x => h x/10) ν := by
    simpa only [div_eq_mul_inv] using (bMeas_integrable ν hh).mul_const (10:ℝ)⁻¹
  have h₂ := (bMeas_integrable ν hh.sq).const_mul (3/4:ℝ)
  have hb := integral_mono_ae (integrable_const (μ:=ν) (β-1/50))
    ((h₁.sub h₂).sub (bMeas_integrable ν hr)) hloc
  change (∫ _ : X, (β-1/50) ∂ν)≤∫ x, h x/10-(3/4)*h x^2-r x ∂ν at hb
  have hi : Integrable (fun x => h x/10-(3/4)*h x^2) ν := h₁.sub h₂
  rw [integral_const,integral_sub hi (bMeas_integrable ν hr),
    integral_sub h₁ h₂,integral_const_mul] at hb
  rw [show (∫ x, h x/10 ∂ν)=Z/10 by
    simp only [div_eq_mul_inv,integral_mul_const,hhs]] at hb
  change mass ν*(β-1/50)≤_ at hb
  rw [hν] at hb
  linarith

#print axioms case_two_average
end SparseHalfGraphon
