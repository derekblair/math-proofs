import OrientedLattice

namespace PermHex

lemma ideal_entries {c s : ℝ} (h : c^2+s^2=1) :
    |(ideal c s).a|≤3 ∧ |(ideal c s).b|≤3 ∧ |(ideal c s).c|≤3 ∧ |(ideal c s).d|≤3 := by
  obtain ⟨hc,hs⟩ := unit_cos_sin_bounds h
  have hs3 := root3_le_two
  have hp := root3_pos
  have hcm := mul_le_mul_of_nonneg_right hc hp.le
  have hsm := mul_le_mul_of_nonneg_right hs hp.le
  have h1 := abs_add_le (c*root3/2) (-(s*3/2))
  have h2 := abs_add_le (s*root3/2) (c*3/2)
  simp only [abs_neg,abs_mul,abs_div,abs_of_pos hp,←sub_eq_add_neg] at h1 h2
  norm_num at h1 h2
  unfold ideal
  dsimp
  rw [abs_mul,abs_of_pos hp,abs_mul,abs_of_pos hp]
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma product_scaled_close {A B u v r ε : ℝ} (hr : 0≤r) (hε : 0≤ε) (h1 : ε≤1)
    (ha : |A-r*u|≤ε*r) (hb : |B-r*v|≤ε*r)
    (hu : |u|≤3) (hv : |v|≤3) :
    |A*B-r^2*u*v|≤7*ε*r^2 := by
  have hB := abs_add_le (B-r*v) (r*v)
  rw [sub_add_cancel,abs_mul,abs_of_nonneg hr] at hB
  have hrV := mul_le_mul_of_nonneg_left hv hr
  have hRε := mul_le_mul_of_nonneg_right h1 hr
  have hb' : |B|≤4*r := by linarith
  have hi := abs_add_le ((A-r*u)*B) (r*u*(B-r*v))
  rw [show (A-r*u)*B+r*u*(B-r*v)=A*B-r^2*u*v by ring] at hi
  simp only [abs_mul,abs_of_nonneg hr] at hi
  have hv1 := mul_le_mul_of_nonneg_right ha (abs_nonneg B)
  have hv2 := mul_le_mul_of_nonneg_left hb' (show 0≤ε*r by positivity)
  have hv3 := mul_le_mul_of_nonneg_left hb (show 0≤r*|u| by positivity)
  have hv4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu hr) (show 0≤ε*r by positivity)
  linarith

lemma det_close {c s r ε : ℝ} {M : Mat} (hU : c^2+s^2=1)
    (hr : 0≤r) (hε : 0≤ε) (he : ε≤1) (h : Close r ε M (ideal c s)) :
    |detR M-r^2*areaUnit|≤14*ε*r^2 := by
  obtain ⟨fa,fb,fc,fd⟩ := ideal_entries hU
  obtain ⟨ha,hb,hc,hd⟩ := h
  have h1 := product_scaled_close hr hε he ha hd fa fd
  have h2 := product_scaled_close hr hε he hb hc fb fc
  let I := ideal c s
  change |M.a*M.d-r^2*I.a*I.d|≤_ at h1
  change |M.b*M.c-r^2*I.b*I.c|≤_ at h2
  have hm := abs_add_le (M.a*M.d-r^2*I.a*I.d) (-(M.b*M.c-r^2*I.b*I.c))
  change |detR M-r^2*areaUnit|≤_
  rw [←ideal_det hU]
  change |detR M-r^2*detR I|≤_
  have hh : detR M-r^2*detR I =
      (M.a*M.d-r^2*I.a*I.d)+ -(M.b*M.c-r^2*I.b*I.c) := by unfold detR; ring
  rw [hh]
  rw [abs_neg] at hm
  linarith

#print axioms det_close
end PermHex
