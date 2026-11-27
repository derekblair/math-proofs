import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace SparseHalfTwoHeavyRigidity

/-- Recover the only candidate endpoint of the two-heavy main chamber. -/
theorem exceptional (h p q r s L : ℝ)
    (hr : 1<r) (hpr : p≤r) (hqr : 3*r/4<q)
    (hL : 0≤L) (hL0 : L≤2/3)
    (hsum : h+p+q+r+s+L=6)
    (hpiv : r+s≤2+h)
    (hc : 2≤p*q+r*(s-1)+L^2/4)
    (hm : 2≤r*(4-max (p+s) (r+q))) :
    h=2/3 ∧ p=3/2 ∧ r=3/2 ∧ q=7/6 ∧ s=7/6 ∧ L=0 := by
  let d := r-p
  let u := p+q
  let v := r+s
  let Δ := h-(2-L)/3
  let D := (r-p)+(q-s)
  have hd : 0≤d := by dsimp [d]; linarith
  have huv : u+v=16/3-(2/3)*L-Δ := by dsimp [u,v,Δ]; linarith
  have hvs : v-u≤3*Δ := by dsimp [u,v,Δ]; linarith
  have hab : 2*d≤|D|+3*Δ := by
    have h := le_abs_self D
    dsimp [d,D] at *
    dsimp [u,v] at hvs
    linarith
  have hmax : max (p+s) (r+q) = (u+v+|D|)/2 := by
    by_cases hh : p+s≤r+q
    · have hh' : 0≤D := by dsimp [D]; linarith
      rw [max_eq_right hh,abs_of_nonneg hh']
      dsimp [u,v,D]; ring
    · have hh' : D≤0 := by dsimp [D]; linarith
      rw [max_eq_left (by linarith : r+q≤p+s),abs_of_nonpos hh']
      dsimp [u,v,D]; ring
  have hi : (p*q+r*(s-1)+L^2/4) + (5/4)*(r*(4-max (p+s) (r+q))) +
      2*(r-3/2)^2 + (r/2)*|D| + L*(r-L)/4 +
      d*(q-3*r/4) + (r/8)*(|D|+3*Δ-2*d) = 9/2 := by
    rw [hmax,huv]
    dsimp [d,Δ]
    linear_combination r * hsum
  have ha0 : 0≤2*(r-3/2)^2 := by positivity
  have ha1 : 0≤(r/2)*|D| := mul_nonneg (by linarith) (abs_nonneg _)
  have ha2 : 0≤L*(r-L)/4 := by
    exact div_nonneg (mul_nonneg hL (by linarith)) (by norm_num)
  have ha3 : 0≤d*(q-3*r/4) := mul_nonneg hd (by linarith)
  have ha4 : 0≤(r/8)*(|D|+3*Δ-2*d) :=
    mul_nonneg (by linarith) (by linarith)
  have hz0 : 2*(r-3/2)^2=0 := by linarith
  have hz1 : (r/2)*|D|=0 := by linarith
  have hz2 : L*(r-L)/4=0 := by linarith
  have hz3 : d*(q-3*r/4)=0 := by linarith
  have hz4 : (r/8)*(|D|+3*Δ-2*d)=0 := by linarith
  have hr' : r=3/2 := by
    have h : (r-3/2)^2=0 := by linarith
    rw [pow_two] at h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).elim id id)
  have hD0 : |D|=0 := (mul_eq_zero.mp hz1).resolve_left (by linarith)
  have hD : D=0 := abs_eq_zero.mp hD0
  have hL' : L=0 := by
    have h : L*(r-L)=0 := by linarith
    exact (mul_eq_zero.mp h).resolve_right (by linarith)
  have hd' : d=0 := (mul_eq_zero.mp hz3).resolve_right (by linarith)
  have hΔ' : |D|+3*Δ-2*d=0 := (mul_eq_zero.mp hz4).resolve_left (by linarith)
  have h0 : Δ=0 := by linarith
  dsimp [d,Δ,D] at hd' h0 hD
  exact ⟨by linarith, by linarith, hr', by linarith, by linarith, hL'⟩

#print axioms exceptional
end SparseHalfTwoHeavyRigidity
