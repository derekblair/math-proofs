import GeometricGap

namespace RobustFolkman.GeometricGap
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem half_page_difference (t : K) (ht : 0<t) :
    pageFactor t t-pageFactor t (t/2)=t^3/((1+t)*(1+t/2)) := by
  have h₁ : 1+t≠0 := ne_of_gt (by positivity)
  have h₂ : 1+t/2≠0 := ne_of_gt (by positivity)
  unfold pageFactor
  field_simp
  ring

theorem effective_cap_page (t : K) (ht : 0<t) (ht1 : t<1) :
    pageFactor t t/(1-t^2)=1-(t/(1+t))^2 := by
  have h₁ : 1+t≠0 := ne_of_gt (by positivity)
  have h₂ : 1-t^2≠0 := by
    have h : 0<(1-t)*(1+t) := mul_pos (sub_pos.mpr ht1) (by positivity)
    nlinarith only [h]
  unfold pageFactor
  field_simp
  ring

theorem page_strictly_smaller_than_edge (t : K) (ht : 0<t) (ht1 : t<1) :
    pageFactor t t<1-t^2 := by
  have p : 0<1+t := by positivity
  have h : t^2 < 2*t^2/(1+t) := by
    apply (lt_div_iff₀ p).2
    have pos := mul_pos (sq_pos_of_pos ht) (sub_pos.mpr ht1)
    nlinarith only [pos]
  unfold pageFactor
  linarith only [h]

/-- Exact window when the edge/triangle/diamond rates and marked
extension share the same logarithmic page increment. No small-o 
remainder is used in this algebraic step. -/
theorem exact_rate_window (E L H : K) (L0 : 0<L) (EL : E<L) (gap : E+3*L<H) :
    ∃ X : K, 0<X ∧ L<X ∧ 2*X<H-(E+L) ∧ 3*X<H+L-(E+L)
      ∧ E+L<3*X ∧ 2*(E+L)-(E+2*L)<2*X := by
  refine ⟨L+(H-(E+3*L))/4, ?_,?_,?_,?_,?_,?_⟩ <;> linarith only [L0,EL,gap]

#print axioms half_page_difference
#print axioms effective_cap_page
#print axioms exact_rate_window
end RobustFolkman.GeometricGap
