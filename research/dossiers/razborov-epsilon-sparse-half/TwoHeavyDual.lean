import OneHeavyPacking

namespace SparseHalfTwoHeavyDual
open SparseHalfLowSmallSide SparseHalfOneHeavyPacking

/-- Convex rebate is superadditive on nonnegative masses, by
concentrating the two blocks before capping. -/
theorem super (x y : ℝ) (hx : 0≤x) (hy : 0≤y) :
    g x+g y≤g (x+y) := by
  by_cases ht : x+y=0
  · have h1 : x=0 := by linarith
    have h2 : y=0 := by linarith
    simp [h1,h2,g0]
  · let s := x+y
    have hs : 0<s := by dsimp [s]; exact lt_of_le_of_ne (by linarith) (Ne.symm ht)
    have hc := isConvex s
    have hxS : x/s*s=x := div_mul_cancel₀ _ hs.ne'
    have hyS : y/s*s=y := div_mul_cancel₀ _ hs.ne'
    have hsum : x/s+y/s=1 := by rw [← add_div]; exact div_self hs.ne'
    have hS : s ∈ Set.Icc 0 s := ⟨hs.le,le_rfl⟩
    have h0 : (0:ℝ) ∈ Set.Icc 0 s := ⟨le_rfl,hs.le⟩
    have hxr := hc s hS 0 h0 (x/s) (y/s)
      (div_nonneg hx hs.le) (div_nonneg hy hs.le) hsum
    have hyr := hc s hS 0 h0 (y/s) (x/s)
      (div_nonneg hy hs.le) (div_nonneg hx hs.le) (by linarith)
    simp only [mul_zero,add_zero,g0,hxS,hyS] at hxr hyr
    change g x+g y≤g s
    linarith [show (x/s+y/s)*g s=g s by rw [hsum,one_mul]]

theorem light_sum (bs : List (ℝ×ℝ)) (θ : ℝ)
    (hh : ∀ z ∈ bs, 0≤z.1 ∧ 0≤z.2 ∧ z.2≤1) :
    (bs.map fun z => z.2*min θ z.1).sum≤g ((bs.map fun z => z.1+z.2).sum) := by
  induction bs with
  | nil => simp [g0]
  | cons z zs ih =>
    obtain ⟨hp,hq,hq1⟩ := hh z (by simp)
    have hz := ih (fun z hz => hh z (by simp [hz]))
    have hnon : 0≤(zs.map fun z => z.1+z.2).sum := by
      apply List.sum_nonneg
      intro x hx
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
      obtain ⟨ha,hb',_⟩ := hh b (by simp [hb])
      linarith
    have hpoint := ge_line (z.1+z.2) z.2 hq hq1
    have hprod := mul_le_mul_of_nonneg_left (min_le_right θ z.1) hq
    have hcomb := super (z.1+z.2) _ (by linarith) hnon
    simp only [List.map_cons,List.sum_cons]
    nlinarith

/-- Two heavy blocks plus arbitrary lights of mass L. The enlargement
from L-1 to g L is the only loss; when L≥2 it vanishes identically. -/
theorem cost_le_remainder (a h p q r s θ L V : ℝ) (ha : a≤4)
    (hθ : 1≤θ) (hq : 1≤q) (hs : 1≤s) (hqp : q≤p) (hsr : s≤r)
    (hB : a+h+p+q+r+s+L=10) (hh : 0≤h) (hL : 0≤L) (hV : V≤g L) :
    q*min θ p+s*min θ r+V-θ*(5-a) ≤ 2 - h - (θ-1)*(4-a+h+L)/2 + (g L-(L-1)) := by
  have hq0 : 0≤q-1 := by linarith
  have hs0 : 0≤s-1 := by linarith
  have h1 := mul_le_mul_of_nonneg_left (min_le_left θ p) hq0
  have h2 := mul_le_mul_of_nonneg_left (min_le_left θ r) hs0
  have h3 := min_le_right θ p
  have h4 := min_le_right θ r
  have hk : q+s-2≤(6-a-h-L)/2 := by linarith
  have hz := mul_le_mul_of_nonneg_right hk (show 0≤θ-1 by linarith)
  nlinarith

#print axioms cost_le_remainder
#print axioms light_sum
end SparseHalfTwoHeavyDual
