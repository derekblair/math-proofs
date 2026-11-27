import TwoHeavyDual
import TwoBlockCertificate

namespace SparseHalfTwoHeavyFinish
open SparseHalfLowSmallSide

/-- Any two-heavy chamber still failing the B-only bound has light mass
below two thirds in the scale where the overall mass is ten. -/
theorem smallLights (a h p q r s θ L V : ℝ)
    (ha : a≤4) (hθ : 1≤θ) (hh : 0≤h) (hL : 0≤L)
    (hq : 1≤q) (hs : 1≤s) (hqp : q≤p) (hsr : s≤r) (hV : V≤g L)
    (hB : a+h+p+q+r+s+L=10)
    (h1 : p+q≤2+h) (h2 : r+s≤2+h)
    (hfail : 2<q*min θ p+s*min θ r+V-θ*(5-a)) :
    L<2/3 ∧ h<(2-L)^2/4 := by
  have hm := SparseHalfTwoHeavyDual.cost_le_remainder a h p q r s θ L V
    ha hθ hq hs hqp hsr hB hh hL hV
  have hneg := mul_nonneg (show 0≤θ-1 by linarith)
    (show 0≤4-a+h+L by linarith)
  have hL2 : L≤2 := by
    by_contra! hn
    rw [eq_large _ hn.le] at hm
    linarith
  rw [eq_small _ hL2] at hm
  have hh' : h<(2-L)^2/4 := by nlinarith
  refine ⟨?_,hh'⟩
  by_contra! hn
  have hh0 : (2-L)/3≤h := by linarith
  have hprod := mul_nonneg (show 0≤2-L by linarith)
    (show 0≤3*L-2 by linarith)
  nlinarith

/-- The three marginal slopes of the two-block term, evaluated at the
two heavy prices. This upper bound does not charge the light rebate. -/
theorem price (p q r s t θ : ℝ)
    (hpr : p≤r) (hqs : t≤q+s) (ht : 0≤t) :
    q*min θ p+s*min θ r-θ*t ≤
      (if s≤t then p*(q+s-t) else p*q+r*(s-t)) := by
  by_cases hθp : θ≤p
  · have hθr : θ≤r := hθp.trans hpr
    rw [min_eq_left hθp,min_eq_left hθr]
    have h0 := mul_le_mul_of_nonneg_right hθp (sub_nonneg.mpr hqs)
    by_cases hst : s≤t
    · rw [if_pos hst]; nlinarith
    · rw [if_neg hst]
      have h1 := mul_le_mul_of_nonneg_right hpr (show 0≤s-t by linarith)
      nlinarith
  · rw [min_eq_right (show p≤θ by linarith)]
    by_cases hθr : θ≤r
    · rw [min_eq_left hθr]
      by_cases hst : s≤t
      · rw [if_pos hst]
        have h0 := mul_nonneg (show 0≤θ-p by linarith) (show 0≤t-s by linarith)
        nlinarith
      · rw [if_neg hst]
        have h0 := mul_le_mul_of_nonneg_right hθr (show 0≤s-t by linarith)
        nlinarith
    · rw [min_eq_right (show r≤θ by linarith)]
      have h0 := mul_le_mul_of_nonneg_right (show r≤θ by linarith) ht
      by_cases hst : s≤t
      · rw [if_pos hst]
        have h1 := mul_nonneg (show 0≤r-p by linarith) (show 0≤t-s by linarith)
        nlinarith
      · rw [if_neg hst]
        nlinarith

theorem smallSecond (p q r s t L : ℝ)
    (hp : 0≤p) (hq : q≤p) (hpr : p≤r)
    (hL0 : 0≤L) (hL : L≤2/3) (hst : s≤t)
    (hcap : 2*(p+q)+r+s+L≤7+t) :
    p*(q+s-t)+L^2/4≤2 := by
  by_contra! hc
  have h0 := mul_le_mul_of_nonneg_left (show q+s-t≤q by linarith) hp
  have hpq : 2-L^2/4<p*q := by linarith
  have hp2 := mul_le_mul_of_nonneg_left hq hp
  have hLs := mul_nonneg hL0 (show 0≤2/3-L by linarith)
  have hp43 : 4/3≤p := by
    by_contra! hn
    have hpp := mul_nonneg hp (show 0≤4/3-p by linarith)
    nlinarith
  have hh := mul_le_mul_of_nonneg_left (show 3*p+q+(q+s-t)+L≤7 by linarith) hp
  have hb := mul_nonneg (show 0≤p-1 by linarith) (show 0≤3*p-4 by linarith)
  have hLp := mul_nonneg hL0 (show 0≤p-L/2 by linarith)
  nlinarith

theorem oblique (p q r s t L : ℝ)
    (ht : 1≤t) (hr : 0≤r) (hpr : p≤r) (hm : r/2≤p)
    (hq : q≤3*r/4) (hL : 0≤L) (hLr : L≤r)
    (hcap : p+q+2*(r+s)+L≤7+t) :
    p*q+r*(s-t)+L^2/4≤2 := by
  have h0 := mul_le_mul_of_nonneg_left (show s-t≤3-r-(p+q+L)/2 by linarith) hr
  have h1 := mul_le_mul_of_nonneg_right hq (show 0≤p-r/2 by linarith)
  have h2 := mul_le_mul_of_nonneg_left hpr (show 0≤r/4 by linarith)
  have h3 := mul_nonneg hL (show 0≤r-L by linarith)
  nlinarith [sq_nonneg (r-4/3)]

theorem chamber (a h p q r s L : ℝ)
    (ha : a≤4) (hr : 0≤r) (hpr : p≤r) (hqr : 3*r/4≤q)
    (hL : 0≤L) (hLr : L≤r)
    (hsum : a+h+p+q+r+s+L=10)
    (hpiv1 : p+q≤2+h) (hpiv2 : r+s≤2+h) :
    (p*q+r*(s-(5-a))+L^2/4) +
      (5/4)*(r*(5-max (p+s) (r+q)-a/4)) ≤ 9/2 := by
  let d := r-p
  let u := p+q
  let v := r+s
  let Δ := h-(6-a-L)/3
  let D := (r-p)+(q-s)
  have hd : 0≤d := by dsimp [d]; linarith
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
  have hu : u+v= 8- (2/3)*a-(2/3)*L-Δ := by dsimp [u,v,Δ]; linarith
  have he : (p*q+r*(s-(5-a))+L^2/4) +
      (5/4)*(r*(5-max (p+s) (r+q)-a/4)) =
      r*(17/4+7*a/16-2*r)-3*r*Δ/8+d*(r-q)-5*r*|D|/8+
        (L^2-r*L)/4 := by
    rw [hmax,hu]
    dsimp [d,Δ]
    linear_combination r * hsum
  rw [he]
  have hdiff := mul_nonneg hr (show 0≤4-a by linarith)
  have habs : 0≤r*|D| := mul_nonneg hr (abs_nonneg _)
  have hprod := mul_nonneg hL (show 0≤r-L by linarith)
  nlinarith [sq_nonneg (r-3/2)]

/-- Every prospective B-only obstruction in the two-heavy chamber
activates the graph-theoretic mixed-orientation profile. -/
theorem finish (a h p q r s θ L V : ℝ)
    (ha0 : 19/5≤a) (ha : a≤4) (hθ : 1≤θ) (hh : 0≤h) (hL : 0≤L)
    (hq : 1≤q) (hs : 1≤s) (hqp : q≤p) (hsr : s≤r) (hpr : p≤r) (hr2 : r≤2)
    (hV : V≤g L) (hB : a+h+p+q+r+s+L=10)
    (h1 : p+q≤2+h) (h2 : r+s≤2+h)
    (hfail : 2<q*min θ p+s*min θ r+V-θ*(5-a)) :
    h+L≤a/2 ∧ r*(5-max (p+s) (r+q)-a/4)≤2 := by
  obtain ⟨hLs,hh'⟩ := smallLights a h p q r s θ L V ha hθ hh hL
    hq hs hqp hsr hV hB h1 h2 hfail
  have hsum : h+L≤a/2 := by
    have he := mul_nonneg hL (show 0≤2/3-L by linarith)
    nlinarith
  have hLr : L≤r := by linarith
  have hprc := price p q r s (5-a) θ hpr (by linarith) (by linarith)
  have hqv : V≤L^2/4 := by rwa [eq_small _ (by linarith)] at hV
  refine ⟨hsum,?_⟩
  by_cases hst : s≤5-a
  · rw [if_pos hst] at hprc
    have hx := smallSecond p q r s (5-a) L (by linarith) hqp hpr
      hL hLs.le hst (by linarith)
    linarith
  · rw [if_neg hst] at hprc
    by_cases hqo : q≤3*r/4
    · have hx := oblique p q r s (5-a) L (by linarith) (by linarith) hpr
        (by linarith) hqo hL hLr (by linarith)
      linarith
    · have hx := chamber a h p q r s L ha (by linarith) hpr (by linarith)
        hL hLr hB h1 h2
      linarith

#print axioms finish
end SparseHalfTwoHeavyFinish
