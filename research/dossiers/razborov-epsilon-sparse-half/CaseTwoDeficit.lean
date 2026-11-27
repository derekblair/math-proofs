import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace SparseHalfCaseTwoDeficit

/-- Razborov's Q1, the endpoint at which the cross density
takes its maximal value b(1-a-b). -/
noncomputable def q1 (a b : ℝ) : ℝ :=
  13/16*a^2 - 9/8*a*b - 3/16*b^2 - a/4 + b/2

noncomputable def f (a : ℝ) : ℝ := a*(1/2-a)/2

/-- Strict losses in the Case 2 completion when B grows above A or
the cross density is below its endpoint. -/
theorem q1_drop (a b : ℝ) :
    q1 a b = f a + ((1-3*a)/2)*(b-a) - 3/16*(b-a)^2 := by
  unfold q1 f
  ring

theorem slack (a b Δ e : ℝ)
    (ha0 : 19/50≤a) (hab : a≤b) (hb : b≤1/2)
    (hΔ : 0≤Δ) (he : f a - 1/50 ≤ e)
    (hbound : 1/50 ≤ q1 a b - (b-a)*Δ/(8*b) - 3*Δ^2/(16*b^2)) :
    (7/100)*(b-a) + (3/4)*Δ^2 ≤ e := by
  have hb0 : 0<b := by linarith
  have hlin := mul_nonneg (show 0≤(3*a-1)/2-7/100 by linarith) (sub_nonneg.mpr hab)
  have hcross : 0≤(b-a)*Δ/(8*b) := div_nonneg (mul_nonneg (sub_nonneg.mpr hab) hΔ)
    (by positivity)
  have hden := mul_nonneg (show 0≤1/2-b by linarith) (show 0≤1/2+b by linarith)
  have hd : 0<16*b^2 := by positivity
  have hco : (3/4)*Δ^2 ≤ 3*Δ^2/(16*b^2) := by
    apply (le_div_iff₀ hd).2
    have hk := mul_nonneg (show 0≤1/4-b^2 by linarith) (sq_nonneg Δ)
    nlinarith
  rw [q1_drop] at hbound
  nlinarith [sq_nonneg (b-a)]

#print axioms slack
end SparseHalfCaseTwoDeficit
