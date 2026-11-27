import CountableHeavy
import TwoHeavyFinish
import TwoHeavyRigidity

namespace SparseHalfCountableEndpoint
open SparseHalfLowSmallSide

/-- In the genuine two-heavy endpoint chamber, the mixed orientation has
a strict certificate unless the one explicit symmetric capacity vector
occurs. The graph-level exact orientation is handled separately. -/
theorem two_heavy_endpoint (h p q r s L V θ : ℝ)
    (hθ : 1≤θ) (hh : 0≤h) (hL : 0≤L)
    (hq : 1<q) (hs : 1<s) (hqp : q≤p) (hsr : s≤r) (hpr : p≤r)
    (hV : V≤g L) (total : h+p+q+r+s+L=6)
    (hpiv : p+q≤2+h) (hriv : r+s≤2+h)
    (bad : 2≤q*min θ p+s*min θ r+V-θ) :
    h+L≤2 ∧
      (r*(4-max (p+s) (r+q))<2 ∨
      (h=2/3 ∧ p=3/2 ∧ r=3/2 ∧ q=7/6 ∧ s=7/6 ∧ L=0)) := by
  have hL2 : L<2 := by linarith
  have cb := SparseHalfTwoHeavyDual.cost_le_remainder 4 h p q r s θ L V
    le_rfl hθ hq.le hs.le hqp hsr (by linarith) hh hL hV
  rw [eq_small _ hL2.le] at cb
  have prod := mul_nonneg (show 0≤θ-1 by linarith) (show 0≤h+L by linarith)
  have hcap : h≤(2-L)^2/4 := by nlinarith
  have hL23 : L≤2/3 := by
    by_contra! no
    have xx := mul_pos (show 0<2-L by linarith) (show 0<3*L-2 by linarith)
    nlinarith
  have sum : h+L≤2 := by
    have xx := mul_nonneg hL (show 0≤2/3-L by linarith)
    nlinarith
  have hV2 : V≤L^2/4 := by rwa [eq_small _ hL2.le] at hV
  have prc := SparseHalfTwoHeavyFinish.price p q r s 1 θ hpr (by linarith) (by norm_num)
  rw [ite_eq_right (not_le.mpr hs)] at prc
  have C : 2≤p*q+r*(s-1)+L^2/4 := by linarith
  have hr : 1<r := hs.trans_le hsr
  have hqr : 3*r/4<q := by
    by_contra! no
    have hrpos : 0≤r := by linarith
    have h0 := mul_le_mul_of_nonneg_left (show s-1≤3-r-(p+q+L)/2 by linarith) hrpos
    have h1 := mul_le_mul_of_nonneg_right no (show 0≤p-r/2 by linarith)
    have h2 := mul_le_mul_of_nonneg_left hpr (show 0≤r/4 by linarith)
    have h3 := mul_nonneg hL (show 0≤r-L by linarith)
    have hr4 : r=4/3 := by
      have w : (r-4/3)^2≤0 := by nlinarith
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm w (sq_nonneg _)))
    linarith
  refine ⟨sum,?_⟩
  by_cases mm : r*(4-max (p+s) (r+q))<2
  · exact Or.inl mm
  · exact Or.inr (SparseHalfTwoHeavyRigidity.exceptional h p q r s L hr hpr hqr hL hL23 total hriv C (le_of_not_gt mm))

#print axioms two_heavy_endpoint
end SparseHalfCountableEndpoint
