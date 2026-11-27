import GeometricSliceMass

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped ENNReal

theorem lower_band_constant (r t W : ℝ) (r3 : 3≤r) (tp : 0<t) (t1 : t≤1/8)
    (d : 1≤4*r*t^2) (wide : 1/(4*r*t)≤W) :
    sliceMass r t 1 ≤ ENNReal.ofReal (2*Real.exp 3)*sliceMass r t (t+W) := by
  have rp : 0<r := by linarith
  refine (slice_mass_cap_upper r t rp tp (by linarith only [t1])).trans ?_
  have lo := slice_mass_band_lower r t W r3 tp t1 d wide
  have e : (2*Real.exp 3)*(Real.exp (-3)*sliceWeight r t/(4*r*t)) =
      sliceWeight r t/(2*r*t) := by
    rw [←mul_div_assoc,show 2*Real.exp 3*(Real.exp (-3)*sliceWeight r t) =
        2*(Real.exp 3*Real.exp (-3))*sliceWeight r t by ring,
      ←Real.exp_add]
    norm_num
    field_simp [rp.ne',tp.ne'] <;> ring
  rw [←e,ENNReal.ofReal_mul (by positivity)]
  gcongr

/-- For a tiny threshold displacement, the intermediate edge mass
is a small, explicit fraction of the tighter cap mass. -/
theorem gap_band_constant (r t s : ℝ) (r3 : 3≤r) (tp : 0<t) (t1 : t≤1/8)
    (d : 1≤4*r*t^2) (s0 : 0≤s) (st : s≤t) :
    sliceMass r (t-s) t ≤
      ENNReal.ofReal (4*r*t*s*Real.exp (3+4*r*t*s))*sliceMass r t 1 := by
  have rp : 0<r := by linarith
  have wide : 1/(4*r*t)≤1-t := by
    have l : 1/(4*r*t)≤t := by
      apply (div_le_iff₀ (by positivity : 0<4*r*t)).2
      nlinarith only [d]
    linarith only [l,t1]
  have lo := slice_mass_band_lower r t (1-t) r3 tp t1 d wide
  rw [add_sub_cancel] at lo
  refine (slice_mass_gap_upper r t s rp.le tp t1 s0 st).trans ?_
  have e : (4*r*t*s*Real.exp (3+4*r*t*s))*(Real.exp (-3)*sliceWeight r t/(4*r*t)) =
      Real.exp (4*r*t*s)*sliceWeight r t*s := by
    rw [←mul_div_assoc,show (4*r*t*s*Real.exp (3+4*r*t*s))*(Real.exp (-3)*sliceWeight r t) =
      (4*r*t)*(Real.exp (3+4*r*t*s)*Real.exp (-3))*sliceWeight r t*s by ring,←Real.exp_add]
    rw [show (3+4*r*t*s)+(-3)=4*r*t*s by ring]
    field_simp [rp.ne',tp.ne'] <;> ring
  rw [←e,ENNReal.ofReal_mul (by positivity)]
  gcongr

#print axioms lower_band_constant
#print axioms gap_band_constant
end RobustFolkman.GeometricGap
