import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace RobustFolkman.GeometricGap

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def pageFactor (t x : K) : K := 1-2*t^2/(1+x)
def bThreeDet (t : K) : K := (1-t^2)*pageFactor t t^3

def subK4Det (t r : K) : K :=
  (1-t^2)*(pageFactor t t^2-(r-2*t^2/(1+t))^2)*pageFactor t r

theorem page_mono_strict {t a b : K} (t0 : 0<t) (ha : -1<a) (hab : a<b) :
    pageFactor t a<pageFactor t b := by
  have ap : 0<1+a := by linarith
  have bp : 0<1+b := by linarith
  have pq : 0<(2:K)*t^2 := by positivity
  have h : 2*t^2/(1+b)<2*t^2/(1+a) := by
    apply (div_lt_div_iff₀ bp ap).2
    exact mul_lt_mul_of_pos_left (by linarith) pq
  unfold pageFactor
  linarith

theorem centered_less {t : K} (t0 : 0<t) (tHalf : t≤1/2) :
    2*t^2/(1+t)<t := by
  have p : 0<1+t := by linarith
  apply (div_lt_iff₀ p).2
  have z := mul_pos t0 (show 0<1-t by linarith)
  nlinarith only [z]

theorem lower_r_gap {t r : K} (t0 : 0<t) (tHalf : t≤1/2)
    (rlo : -1<r) (rhi : r≤t) (p0 : 0≤pageFactor t r) :
    subK4Det t r<bThreeDet t := by
  have den := centered_less t0 tHalf
  have f0 : 0<pageFactor t t := by unfold pageFactor; linarith
  have b0 : 0<1-t^2 := by
    have p := mul_pos (show 0<1-t by linarith) (show 0<1+t by linarith)
    nlinarith only [p]
  unfold subK4Det bThreeDet
  rw [mul_assoc]
  apply mul_lt_mul_of_pos_left _ b0
  rcases lt_or_eq_of_le rhi with rlt|rEq
  · apply lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (show pageFactor t t^2-(r-2*t^2/(1+t))^2≤pageFactor t t^2 by
        linarith [sq_nonneg (r-2*t^2/(1+t))]) p0)
    have lt := mul_lt_mul_of_pos_left (page_mono_strict t0 rlo rlt) (sq_pos_of_pos f0)
    simpa [pow_succ] using lt
  · subst r
    have q : 0<(t-2*t^2/(1+t))^2 := sq_pos_of_pos (by linarith)
    have lt := mul_lt_mul_of_pos_right
      (show pageFactor t t^2-(t-2*t^2/(1+t))^2<pageFactor t t^2 by linarith) f0
    simpa [pow_succ] using lt

def comparisonPoly (t h : K) : K :=
  (1+t)^2*h^2 + (1+t^2*(1-2*t^2)+5*t*(1-t^2))*h +
    2*t*(1-(2*t-t^2)^2)

theorem comparison_identity {t r : K} (tp : 0<1+t) (rp : 0<1+r) :
    (subK4Det t t-subK4Det t r)*(1+r)*(1+t) =
      (r-t)*(1-t)*comparisonPoly t (r-t) := by
  unfold subK4Det pageFactor comparisonPoly
  field_simp [ne_of_gt tp,ne_of_gt rp]
  <;> ring

theorem comparison_nonneg {t h : K} (t0 : 0<t) (tHalf : t≤1/2) (hn : 0≤h) :
    0≤comparisonPoly t h := by
  have t2 : t^2≤1/4 := by
    have p := mul_nonneg (show 0≤1/2-t by linarith) (show 0≤1/2+t by positivity)
    nlinarith only [p]
  have t22 : 0≤1-2*t^2 := by linarith
  have t21 : 0≤1-t^2 := by linarith
  have e0 : 0≤2*t-t^2 := by
    have p := mul_nonneg t0.le (show 0≤2-t by linarith)
    nlinarith only [p]
  have e1 : 2*t-t^2≤1 := by nlinarith only [tHalf,sq_nonneg t]
  have eo : 0≤1-(2*t-t^2)^2 := by
    have p := mul_nonneg (sub_nonneg.mpr e1) (show 0≤1+(2*t-t^2) by linarith)
    nlinarith only [p]
  unfold comparisonPoly
  positivity

theorem upper_r_comparison {t r : K} (t0 : 0<t) (tHalf : t≤1/2) (tr : t≤r) :
    subK4Det t r≤subK4Det t t := by
  have tp : 0<1+t := by linarith
  have rp : 0<1+r := by linarith
  have rp1 : 0≤r-t := by linarith
  have tp1 : 0≤1-t := by linarith
  have hp := mul_nonneg (mul_nonneg rp1 tp1) (comparison_nonneg t0 tHalf rp1)
  rw [←comparison_identity tp rp, mul_assoc] at hp
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_left hp (mul_pos rp tp))

/-- Fixed-edge Schur-complement envelope for H has strictly lower
maximal determinant than a three-page book. The graph/matrix bridge
and edge saturation are separate from this scalar theorem. -/
theorem subK4_gap {t r : K} (t0 : 0<t) (tHalf : t≤1/2)
    (rlo : -1<r) (p0 : 0≤pageFactor t r) : subK4Det t r<bThreeDet t := by
  by_cases h : r≤t
  · exact lower_r_gap t0 tHalf rlo h p0
  · have ft : 0≤pageFactor t t := by
      unfold pageFactor
      have den := centered_less t0 tHalf
      linarith
    exact (upper_r_comparison t0 tHalf (le_of_not_ge h)).trans_lt
      (lower_r_gap t0 tHalf (by linarith) le_rfl ft)

#print axioms subK4_gap
end RobustFolkman.GeometricGap
