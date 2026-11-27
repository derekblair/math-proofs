import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter Topology
namespace SparseHalfGraphon

noncomputable def greedyCaseTwo (a b c : ℝ) : ℝ :=
  (1/2-a)*(b-a) +(1/4)*(1/2-b-c/(2*b))*(1/2+b+3*(c/(2*b))) +
    ((1/2-a+b/2)*c/2-(b/2)*(1/2-a)*(1-a-b))/b

noncomputable def greedyCaseOne (a b : ℝ) : ℝ :=
  (1/2-a)*(b-a)+b*(1/2-b)/2

/-- Exact expression for the loss of Razborov's Case 2 second moment
when the grown set is bigger or the cross-density is below saturation. -/
theorem greedy_case_two_identity (a b c : ℝ) (hb : b≠0) :
    greedyCaseTwo a b c =
      a*(1/2-a)/2 + ((1-3*a)/2)*(b-a) - (3/16)*(b-a)^2
      - (b-a)*(b*(1-a-b)-c)/(8*b) - (3/16)*(b*(1-a-b)-c)^2/b^2 := by
  unfold greedyCaseTwo
  field_simp
  <;> ring

/-- The two scalar cases give a uniform negative slope near the endpoint. -/
theorem greedy_loss_near_endpoint (a b c : ℝ) (ha : 39/100≤a) (hab : a≤b)
    (hc : c≤b*(1-a-b)) :
    max (greedyCaseOne a b) (greedyCaseTwo a b c) ≤
      a*(1/2-a)/2-(3/100)*(b-a) := by
  have hb : 0<b := by linarith
  apply max_le
  · unfold greedyCaseOne
    have hx := mul_nonneg (sub_nonneg.mpr hab) (show 0≤3*a/2+b/2-39/50 by linarith)
    nlinarith only [hx]
  · rw [greedy_case_two_identity a b c hb.ne']
    have hcross := div_nonneg (mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hc))
      (show 0≤8*b by positivity)
    have hsq := div_nonneg (mul_nonneg (by norm_num : 0≤(3:ℝ)/16) (sq_nonneg (b*(1-a-b)-c))) (sq_nonneg b)
    have hlin := mul_nonneg (sub_nonneg.mpr hab) (show 0≤(3*a-1)/2-3/100 by linarith)
    nlinarith only [hcross,hsq,hlin,sq_nonneg (b-a)]

#print axioms greedy_case_two_identity
#print axioms greedy_loss_near_endpoint
end SparseHalfGraphon
