import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace SparseHalfTwoBlockCertificate

/-- Explicit quadratic certificate for the main two-block chamber.
p≤r are larger sides, q,s the smaller sides; h is outside isolated mass.
The weighted average of the outside-only and one-sided signature costs
is at most two. Here masses have been scaled by ten. -/
theorem chamber (a h p q r s : ℝ)
    (ha : a≤4) (hr : 0≤r) (hpr : p≤r)
    (hqr : 3*r/4≤q)
    (hsum : a+h+p+q+r+s=10)
    (hpiv1 : p+q≤2+h) (hpiv2 : r+s≤2+h) :
    (p*q+r*(s-(5-a))) +
      (5/4)*(r*(5-max (p+s) (r+q)-a/4)) ≤ 9/2 := by
  let d := r-p
  let u := p+q
  let v := r+s
  let Δ := h-(6-a)/3
  let D := (r-p)+(q-s)
  have hd : 0≤d := by dsimp [d]; linarith
  have hΔ : 0≤Δ := by dsimp [Δ]; linarith
  have hvs : v-u≤3*Δ := by dsimp [u,v,Δ]; linarith
  have hdu : d≤ (|D|+3*Δ)/2 := by
    have h := le_abs_self D
    dsimp [d,D] at *
    dsimp [u,v] at hvs
    linarith
  have herror : d*(r-q)≤r*|D|/8+3*r*Δ/8 := by
    have h1 := mul_le_mul_of_nonneg_left (show r-q≤r/4 by linarith) hd
    have h2 := mul_le_mul_of_nonneg_right hdu (show 0≤r/4 by linarith)
    nlinarith
  have hmax : max (p+s) (r+q) = (u+v+|D|)/2 := by
    by_cases hh : p+s≤r+q
    · have hh' : 0≤D := by dsimp [D]; linarith
      rw [max_eq_right hh,abs_of_nonneg hh']
      dsimp [u,v,D]; ring
    · have hh' : D≤0 := by dsimp [D]; linarith
      rw [max_eq_left (by linarith : r+q≤p+s),abs_of_nonpos hh']
      dsimp [u,v,D]; ring
  have hu : u+v= 8- (2/3)*a-Δ := by dsimp [u,v,Δ]; linarith
  have he : p*q+r*(s-(5-a)) +
      (5/4)*(r*(5-max (p+s) (r+q)-a/4)) =
      r*(17/4+7*a/16-2*r)-3*r*Δ/8+d*(r-q)-5*r*|D|/8 := by
    rw [hmax,hu]
    dsimp [d,Δ]
    linear_combination r * hsum
  rw [he]
  have hdiff := mul_nonneg hr (show 0≤4-a by linarith)
  have habs : 0≤r*|D| := mul_nonneg hr (abs_nonneg _)
  nlinarith [sq_nonneg (r-3/2)]

#print axioms chamber
end SparseHalfTwoBlockCertificate
