import TwoHeavyStrict
import MixedOrientation

namespace SparseHalfCountableEndpoint
open SparseHalfLowSmallSide

private theorem mixed_cross (x S X l r R : ℝ)
    (hx : 1≤x) (hx' : x≤2) (hX : 2≤X) (hSX : X≤S) (hS : S≤4)
    (hl : 0≤l) (hr : 0≤r) (hlR : l≤R) (hrR : r≤R) (strict : R*(4-X)<2) :
    ∃ C<2, FourCellFill x (5-S) (min l r) (max l r) C := by
  have cmp := mul_le_mul_of_nonneg_right (max_le hlR hrR) (show 0≤4-X by linarith)
  exact mixed_from_endpoint x S X (min l r) (max l r) hx hx' hX hSX hS
    (le_min hl hr) ((min_le_left ..).trans (le_max_left ..)) (cmp.trans_lt strict)

/-- Full numerical profile for either favorable orientation. One of
the two classes is favorable because its zero-incidence A cell has mass
at least 1; that set-theoretic fact is separate from these allocations. -/
theorem two_heavy_profiles_of_scalar (h p q r s L x : ℝ)
    (hq : 1<q) (hs : 1<s) (hqp : q≤p) (hsr : s≤r) (hpr : p≤r) (hr2 : r≤2)
    (hscalar : r*(4-max (p+s) (r+q))<2 ∨
      (h=2/3 ∧ p=3/2 ∧ r=3/2 ∧ q=7/6 ∧ s=7/6 ∧ L=0)) (hx : 1≤x) (hx' : x≤2) :
    (∃ C<2, FourCellFill x (5-(p+r)) p r C) ∧
      ((∃ C<2, FourCellFill x (5-(p+s)) (min p s) (max p s) C) ∨
       (∃ C<2, FourCellFill x (5-(r+q)) (min r q) (max r q) C)) := by
  rcases hscalar with hm | he
  · have hn : 2≤max (p+s) (r+q) := (show 2≤p+s by linarith).trans (le_max_left ..)
    have hc : max (p+s) (r+q)≤p+r := max_le (by linarith) (by linarith)
    constructor
    · exact mixed_from_endpoint x (p+r) _ p r hx hx' hn hc (by linarith) (by linarith) hpr hm
    · rcases le_total (p+s) (r+q) with hc' | hc'
      · rw [max_eq_right hc'] at hn hm
        exact Or.inr (mixed_cross x (r+q) _ r q r hx hx' hn le_rfl (by linarith)
          (by linarith) (by linarith) le_rfl (hqp.trans hpr) hm)
      · rw [max_eq_left hc'] at hn hm
        exact Or.inl (mixed_cross x (p+s) _ p s r hx hx' hn le_rfl (by linarith)
          (by linarith) (by linarith) hpr hsr hm)
  · obtain ⟨_,rfl,rfl,rfl,rfl,_⟩ := he
    constructor
    · refine ⟨3/2,by norm_num,?_⟩
      convert mixed_exceptional_aligned x hx hx' using 1 <;> norm_num
    · apply Or.inl
      refine ⟨5/3,by norm_num,?_⟩
      convert mixed_exceptional_crossed x hx hx' using 1 <;> norm_num

theorem two_heavy_profiles (h p q r s L V θ x : ℝ)
    (hθ : 1≤θ) (hh : 0≤h) (hL : 0≤L)
    (hq : 1<q) (hs : 1<s) (hqp : q≤p) (hsr : s≤r) (hpr : p≤r) (hr2 : r≤2)
    (hV : V≤g L) (total : h+p+q+r+s+L=6)
    (hpiv : p+q≤2+h) (hriv : r+s≤2+h)
    (bad : 2≤q*min θ p+s*min θ r+V-θ) (hx : 1≤x) (hx' : x≤2) :
    (∃ C<2, FourCellFill x (5-(p+r)) p r C) ∧
      ((∃ C<2, FourCellFill x (5-(p+s)) (min p s) (max p s) C) ∨
       (∃ C<2, FourCellFill x (5-(r+q)) (min r q) (max r q) C)) := by
  have outcome := two_heavy_endpoint h p q r s L V θ hθ hh hL hq hs hqp hsr hpr hV total hpiv hriv bad
  exact two_heavy_profiles_of_scalar h p q r s L x hq hs hqp hsr hpr hr2 outcome.2 hx hx'

#print axioms two_heavy_profiles
end SparseHalfCountableEndpoint
