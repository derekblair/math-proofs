import TwoBlockCertificate

namespace SparseHalfTwoBlockChambers

/-- Removing the entire second small side first leaves the first price.
The pivot on the first block applies whenever this cost could exceed 2. -/
theorem lowSecond (p q r s t : ℝ)
    (hp : 0≤p) (hp2 : p≤2) (hq : q≤p) (hpr : p≤r)
    (hst : s≤t) (hno : 1≤q → 2*(p+q)+r+s≤7+t) :
    p*(q+s-t)≤2 := by
  by_contra! hc
  have h0 := mul_le_mul_of_nonneg_left (show q+s-t≤q by linarith) hp
  have hpq : 2<p*q := by linarith
  have hq1 : 1≤q := by
    by_contra! hq1
    have h1 := mul_le_mul_of_nonneg_left (le_of_lt hq1) hp
    nlinarith
  have hp2' := mul_le_mul_of_nonneg_left hq hp
  have hp43 : 4/3≤p := by
    by_contra! hn
    have hh := mul_nonneg hp (show 0≤4/3-p by linarith)
    nlinarith
  have hh : 3*p+q+(q+s-t)≤7 := by linarith [hno hq1]
  have hb := mul_le_mul_of_nonneg_left hh hp
  have hf := mul_nonneg (show 0≤p-1 by linarith) (show 0≤3*p-4 by linarith)
  nlinarith

/-- Near a single heavy component (including the C5 endpoint) the
outside-only half already suffices. -/
theorem smallFirst (p q r s t : ℝ)
    (hp : 0≤p) (hq : 0≤q) (ht : 1≤t) (hs : t≤s) (hr : s≤r)
    (hu : p+q≤12/5) (hno : p+q+2*(r+s)≤7+t) :
    p*q+r*(s-t)≤2 := by
  let u := p+q
  let v := r+s
  have hu0 : 0≤u := by dsimp [u]; linarith
  have hule : u≤12/5 := hu
  have hv0 : 0≤v := by dsimp [v]; linarith
  have hvt : 0≤v-2*t := by dsimp [v]; linarith
  have hvm : v≤(7+t-u)/2 := by dsimp [u,v]; linarith
  have hvmt : v-2*t≤(7-3*t-u)/2 := by linarith
  have hpos : 0≤(7-3*t-u)/2 := hvt.trans hvmt
  have hb := mul_le_mul hvm hvmt hvt (show 0≤(7+t-u)/2 by linarith)
  have hF := mul_nonneg (show 0≤t-1 by linarith)
    (show 0≤20-2*u+3*(t-1) by linarith)
  have hP := mul_nonneg hu0 (show 0≤12/5-u by linarith)
  have hD := mul_nonneg (show 0≤t by linarith) (show 0≤r-s by linarith)
  have ht1 : p*q+r*(s-t) ≤ u^2/4+v*(v-2*t)/4 := by
    dsimp [u,v]
    nlinarith [sq_nonneg (p-q),sq_nonneg (r-s)]
  nlinarith

/-- The small q≤1 fringe cannot contribute a violation. -/
theorem smallQ (p q r s t : ℝ)
    (ht : 1≤t) (hr : p≤r) (hq : q≤1)
    (hu : 12/5≤p+q) (hno : p+q+2*(r+s)≤7+t) :
    p*q+r*(s-t)≤2 := by
  have hp : 7/5≤p := by linarith
  have hp0 : 0≤p := by linarith
  have hcap : r+s≤(7+t-(p+q))/2 := by linarith
  have hpr : 0≤p+r-(r+s)+t := by linarith
  have hh := mul_nonneg (sub_nonneg.mpr hr) hpr
  have hc : p*q+r*(s-t)≤p*(q+(r+s)-p-t) := by nlinarith
  have hv := mul_le_mul_of_nonneg_left
    (show q+(r+s)-p-t≤(7-3*p)/2 by linarith) hp0
  have hb := mul_nonneg (show 0≤p-7/5 by linarith)
    (show 0≤(3*p/2)-7/5 by linarith)
  nlinarith

/-- The oblique small q fringe is certified by one square. -/
theorem oblique (p q r s t : ℝ)
    (ht : 1≤t) (hr : 0≤r) (hpr : p≤r) (hm : r/2≤p)
    (hq : q≤3*r/4) (hno : p+q+2*(r+s)≤7+t) :
    p*q+r*(s-t)≤2 := by
  have h0 := mul_le_mul_of_nonneg_left
    (show s-t≤3-r-(p+q)/2 by linarith) hr
  have h1 := mul_le_mul_of_nonneg_right hq
    (show 0≤p-r/2 by linarith)
  have h2 := mul_le_mul_of_nonneg_left hpr (show 0≤r/4 by linarith)
  nlinarith [sq_nonneg (r-4/3)]

/-- Complete scalar dichotomy for two outside complementary blocks plus
isolated outside mass. The unsolved general graph problem does not enter. -/
theorem twoBlock (a h p q r s : ℝ)
    (ha : a≤4) (hp : 0≤p) (hq0 : 0≤q) (hq : q≤p)
    (hpr : p≤r) (hr2 : r≤2) (hs : s≤r)
    (hsum : a+h+p+q+r+s=10) :
    (1≤q ∧ 2+h≤p+q) ∨ (1≤s ∧ 2+h≤r+s) ∨
    (if s≤5-a then p*(q+s-(5-a)) else p*q+r*(s-(5-a)))≤2 ∨
    r*(5-max (p+s) (r+q)-a/4)≤2 := by
  by_cases hu : 1≤q ∧ 2+h≤p+q
  · exact Or.inl hu
  by_cases hv : 1≤s ∧ 2+h≤r+s
  · exact Or.inr (Or.inl hv)
  right; right
  have hr0 : 0≤r := hp.trans hpr
  let t := 5-a
  have ht : 1≤t := by dsimp [t]; linarith
  change (if s≤t then p*(q+s-t) else p*q+r*(s-t))≤2 ∨ _
  by_cases hst : s≤t
  · rw [if_pos hst]
    left
    refine lowSecond p q r s t hp (hpr.trans hr2) hq hpr hst ?_
    intro H
    have hh : p+q≤2+h := by by_contra! H'; exact hu ⟨H,H'.le⟩
    dsimp [t]; linarith
  · rw [if_neg hst]
    have hts : t≤s := by linarith
    have hs1 : 1≤s := ht.trans hts
    have hv' : r+s≤2+h := by by_contra! H'; exact hv ⟨hs1,H'.le⟩
    have hv'' : p+q+2*(r+s)≤7+t := by dsimp [t]; linarith
    by_cases hsmall : p+q≤12/5
    · exact Or.inl (smallFirst p q r s t hp hq0 ht hts hs hsmall hv'')
    by_cases hq1 : q≤1
    · exact Or.inl (smallQ p q r s t ht hpr hq1 (by linarith) hv'')
    by_cases hob : q≤3*r/4
    · exact Or.inl (oblique p q r s t ht hr0 hpr (by linarith) hob hv'')
    have hu' : p+q≤2+h := by by_contra! H'; exact hu ⟨by linarith,H'.le⟩
    have H := SparseHalfTwoBlockCertificate.chamber a h p q r s ha hr0 hpr
      (by linarith) hsum hu' hv'
    by_contra! hh
    have hfirst := hh.1
    change 2 < p*q+r*(s-(5-a)) at hfirst
    linarith [hh.1,hh.2]

#print axioms twoBlock
end SparseHalfTwoBlockChambers
