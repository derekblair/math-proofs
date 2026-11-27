import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace PermanentPivotMoment

theorem compress_two_positive_coordinates (x y a b c : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x+y)^2 + a*(x+y)+c ≤ x^2+y^2+2*x*y+a*x+b*y+c ∨
    (x+y)^2 + b*(x+y)+c ≤ x^2+y^2+2*x*y+a*x+b*y+c := by
  rcases le_total a b with h | h
  · exact Or.inl (by nlinarith [mul_nonneg (sub_nonneg.mpr h) hy])
  · exact Or.inr (by nlinarith [mul_nonneg (sub_nonneg.mpr h) hx])

theorem pivot_factor (p u v : ℝ) (hp : p ≤ 1/2) (hvu : v ≤ u)
    (hbase : (u+v)/2 ≤ 1) : p*u+(1-p)*v ≤ 1 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hvu)]

theorem unthinned_baseline_checks :
    (1325 / 1000 : ℚ)^3 ≥ (1325/1000) + 1 ∧
    (1568 / 1000 : ℚ)^3 ≥ (3/2) * ((1568/1000)+1) := by
  norm_num

theorem thinned_pivot_factor (p₁ p₂ p₃ a c d u w : ℝ)
    (h₁ : 0 ≤ p₁) (h₃ : 0 ≤ p₃) (hd : 0 ≤ d)
    (hp : p₂ ≤ u*p₁ + w*p₃) (ha : d*u ≤ a) (hc : d*w ≤ c) :
    d*p₂ ≤ a*p₁ + c*p₃ := by
  have h := mul_le_mul_of_nonneg_left hp hd
  have g₁ := mul_le_mul_of_nonneg_right ha h₁
  have g₃ := mul_le_mul_of_nonneg_right hc h₃
  nlinarith

def soundParameters (q B t : ℚ) : Prop :=
  1 ≤ B ∧ 0 < t ∧ t ≤ 1 ∧
  0 ≤ q/B^2-1 ∧
  (q/B^2-1)/t ≤ 1-1/B ∧
  (q/B^2-1)*t ≤ 1-q/B^3

theorem complex_certificate : soundParameters 2 (13112/10000) (6889/10000) := by
  norm_num [soundParameters]

theorem real_certificate : soundParameters 3 (15451/10000) (14549/20000) := by
  norm_num [soundParameters]

end PermanentPivotMoment

#print axioms PermanentPivotMoment.compress_two_positive_coordinates
#print axioms PermanentPivotMoment.pivot_factor
#print axioms PermanentPivotMoment.unthinned_baseline_checks
#print axioms PermanentPivotMoment.thinned_pivot_factor
#print axioms PermanentPivotMoment.complex_certificate
#print axioms PermanentPivotMoment.real_certificate
