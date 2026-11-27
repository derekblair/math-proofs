import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace DaviesClipping

theorem saddle_at_zero_margin (t : ℝ) (h : 0 ≤ t) :
    (1+t)^2*(1-t^2) ≤ 27/16 := by
  have hs : 0 ≤ (t-1/2)^2 * (t^2+3*t+11/4) := by
    exact mul_nonneg (sq_nonneg _) (by nlinarith [sq_nonneg t])
  nlinarith

theorem saddle_at_one_half :
    (1+(1/2:ℝ))^2*(1-(1/2)^2) = 27/16 := by norm_num

theorem shifted_cut_relaxation (x y a δ : ℝ)
    (hx : x < a) (hy : y ≤ x+δ) : y < a+δ := by linarith

theorem relaxed_radius (ε δ : ℝ) :
    (1-ε)/2 + δ = (1-(ε-2*δ))/2 := by ring

theorem bounded_coordinate (t w α : ℝ)
    (ht : 0 ≤ t) (htu : t ≤ 55/100)
    (hw : 0 ≤ w) (hwu : w ≤ 4/100)
    (_hα : 0 ≤ α) (hαu : α ≤ 133/80) :
    α * (t+w) < 1 := by
  have he : t+w ≤ (59/100:ℝ) := by linarith
  have hh := mul_le_mul hαu he (add_nonneg ht hw) (by norm_num : 0 ≤ (133/80:ℝ))
  nlinarith

theorem paired_cut_separation (x y s a h : ℝ)
    (hx : x < (s-a)/2 + h) (hy : y > -(s-a)/2 + h) :
    a < s+y-x := by linarith

end DaviesClipping

#print axioms DaviesClipping.saddle_at_zero_margin
#print axioms DaviesClipping.saddle_at_one_half
#print axioms DaviesClipping.shifted_cut_relaxation
#print axioms DaviesClipping.relaxed_radius
#print axioms DaviesClipping.bounded_coordinate
#print axioms DaviesClipping.paired_cut_separation
