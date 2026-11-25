import Mathlib.Tactic
import Mathlib.Data.Int.ModEq

namespace PermCircles

def order (m b : ℤ) : ℤ := (2*m+1)*b-m
def slope (b : ℤ) : ℤ := 1-2*b

lemma inverse_slope (m b : ℤ) : (2*m+1)*slope b = 1-2*order m b := by
  unfold slope order
  ring

lemma euclidean_lower {m b a c : ℤ} (hm : 1 ≤ m) (hb : m+1 ≤ b)
    (hbq : 3*m^2 ≤ (b-1)^2)
    (hn : a ≠ 0 ∨ c ≠ 0) :
    (2*m)^2 ≤ ((2*m+1)*a+m*c)^2 + (a+b*c)^2 := by
  let x := (2*m+1)*a+m*c
  let y := a+b*c
  change (2*m)^2 ≤ x^2+y^2
  by_contra! h
  have hx1 : -(2*m) < x := by
    by_contra! hh
    have hh' := mul_nonneg (show 0 ≤ -(2*m)-x by omega) (show 0 ≤ -(2*m)+x*(-1) + 4*m by nlinarith)
    nlinarith [sq_nonneg y]
  have hx2 : x < 2*m := by
    by_contra! hh
    have hh' := mul_nonneg (show 0 ≤ x-2*m by omega) (show 0 ≤ x+2*m by omega)
    nlinarith [sq_nonneg y]
  have hy1 : -(2*m) < y := by
    by_contra! hh
    have hh' := mul_nonneg (show 0 ≤ -y-2*m by omega) (show 0 ≤ -y+2*m by omega)
    nlinarith [sq_nonneg x]
  have hy2 : y < 2*m := by
    by_contra! hh
    have hh' := mul_nonneg (show 0 ≤ y-2*m by omega) (show 0 ≤ y+2*m by omega)
    nlinarith [sq_nonneg x]
  have hD : 0 < order m b := by
    unfold order
    nlinarith [mul_nonneg (show 0 ≤ m by omega) (show 0 ≤ b-1 by omega)]
  have he : (2*m+1)*y-x = order m b*c := by
    dsimp [x,y,order]
    ring
  have hbig : (2*m+1)*(2*m-1)+(2*m-1) < 2*order m b := by
    unfold order
    have hb' : 0 ≤ (2*m+1)*(b-m-1) := mul_nonneg (by omega) (by omega)
    nlinarith
  have hc1 : -2 < c := by
    by_contra! hc
    have ht : 0 ≤ order m b*(-2-c) := mul_nonneg (le_of_lt hD) (by omega)
    have hv : 0 ≤ (2*m+1)*(y+(2*m-1)) := mul_nonneg (by omega) (by omega)
    nlinarith
  have hc2 : c < 2 := by
    by_contra! hc
    have ht : 0 ≤ order m b*(c-2) := mul_nonneg (le_of_lt hD) (by omega)
    have hv : 0 ≤ (2*m+1)*((2*m-1)-y) := mul_nonneg (by omega) (by omega)
    nlinarith
  have hc : c = -1 ∨ c = 0 ∨ c = 1 := by omega
  rcases hc with hc|hc|hc
  · have ha : 0 ≤ a ∧ a ≤ 1 := by
      change -(2*m) < (2*m+1)*a+m*c at hx1
      change (2*m+1)*a+m*c < 2*m at hx2
      rw [hc] at hx1 hx2
      constructor
      · by_contra! hh
        nlinarith [mul_nonneg (show 0 ≤ 2*m+1 by omega) (show 0 ≤ -1-a by omega)]
      · by_contra! hh
        nlinarith [mul_nonneg (show 0 ≤ 2*m+1 by omega) (show 0 ≤ a-2 by omega)]
    have ha' : a = 0 ∨ a = 1 := by omega
    rcases ha' with ha'|ha' <;> simp [x,y,hc,ha'] at h <;> nlinarith [mul_nonneg (show 0 ≤ b-1 by omega) (show 0 ≤ 2*b-1 by omega)]
  · rcases hn with hn|hn
    · change -(2*m) < (2*m+1)*a+m*c at hx1
      change (2*m+1)*a+m*c < 2*m at hx2
      rw [hc] at hx1 hx2
      by_cases ha : a ≤ -1
      · nlinarith [mul_nonneg (show 0 ≤ 2*m+1 by omega) (show 0 ≤ -1-a by omega)]
      · nlinarith [mul_nonneg (show 0 ≤ 2*m+1 by omega) (show 0 ≤ a-1 by omega)]
    · contradiction
  · have ha : -1 ≤ a ∧ a ≤ 0 := by
      change -(2*m) < (2*m+1)*a+m*c at hx1
      change (2*m+1)*a+m*c < 2*m at hx2
      rw [hc] at hx1 hx2
      constructor
      · by_contra! hh
        nlinarith [mul_nonneg (show 0 ≤ 2*m+1 by omega) (show 0 ≤ -2-a by omega)]
      · by_contra! hh
        nlinarith [mul_nonneg (show 0 ≤ 2*m+1 by omega) (show 0 ≤ a-1 by omega)]
    have ha' : a = -1 ∨ a = 0 := by omega
    rcases ha' with ha'|ha' <;> simp [x,y,hc,ha'] at h <;> nlinarith [mul_nonneg (show 0 ≤ b-1 by omega) (show 0 ≤ 2*b-1 by omega)]

#print axioms euclidean_lower
end PermCircles
