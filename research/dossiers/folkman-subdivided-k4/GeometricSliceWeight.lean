import GeometricShellWeight

namespace RobustFolkman.GeometricGap

theorem one_sub_weight_rpow (y d r : ℝ) (d0 : 0≤d) (d2 : d≤1/2)
    (r0 : 0≤r) (lo : 1-d≤y) :
    Real.exp (-2*r*d)≤y^r := by
  have yp : 0<y := (show 0<1-d by linarith).trans_le lo
  have ratio : y⁻¹≤1+2*d := by
    apply (inv_le_iff_one_le_mul₀ yp).2
    have h := mul_le_mul_of_nonneg_right lo (show 0≤1+2*d by positivity)
    have j := mul_nonneg d0 (show 0≤1-2*d by linarith)
    nlinarith only [h,j]
  have l := Real.one_sub_inv_le_log_of_pos yp
  have z := mul_le_mul_of_nonneg_right (show -2*d≤Real.log y by linarith only [ratio,l]) r0
  rw [Real.rpow_def_of_pos yp]
  exact Real.exp_le_exp.mpr (by nlinarith only [z])

theorem one_sub_weight_rpow_upper (y d r : ℝ) (y0 : 0≤y) (rp : 0<r) (hi : y≤1-d) :
    y^r ≤ Real.exp (-r*d) := by
  rcases y0.eq_or_lt with eq|yp
  · rw [←eq,Real.zero_rpow rp.ne']; positivity
  · rw [Real.rpow_def_of_pos yp]
    have l := Real.log_le_sub_one_of_pos yp
    apply Real.exp_le_exp.mpr
    have z := mul_le_mul_of_nonneg_right (show Real.log y≤-d by linarith only [hi,l]) rp.le
    nlinarith only [z]

noncomputable def sliceWeight (r x : ℝ) : ℝ := (1-x^2)^r

theorem slice_weight_upper_exp (r t x : ℝ) (rp : 0<r) (t0 : 0≤t) (tx : t≤x) (x1 : x≤1)
    (t1 : t<1) :
    sliceWeight r x ≤ Real.exp (-(2*r*t)*(x-t))*sliceWeight r t := by
  have xb := pow_le_pow_left₀ (t0.trans tx) x1 2
  have tb : 0<1-t^2 := by nlinarith only [mul_pos (sub_pos.mpr t1) (show 0<1+t by positivity)]
  have x0 : 0≤1-x^2 := by linarith only [xb]
  have q : (1-x^2)/(1-t^2)≤1-2*t*(x-t) := by
    apply (div_le_iff₀ tb).2
    have a := sq_nonneg (x-t)
    have b := mul_nonneg (sq_nonneg t) (show 0≤2*t*(x-t) by positivity)
    nlinarith only [a,b]
  have pp := one_sub_weight_rpow_upper ((1-x^2)/(1-t^2)) (2*t*(x-t)) r
    (div_nonneg x0 tb.le) rp q
  have mm := mul_le_mul_of_nonneg_left pp (Real.rpow_nonneg tb.le r)
  unfold sliceWeight
  rw [←Real.mul_rpow tb.le (div_nonneg x0 tb.le),
    show (1-t^2)*((1-x^2)/(1-t^2))=1-x^2 from by field_simp [tb.ne']] at mm
  rw [show -r*(2*t*(x-t))= -(2*r*t)*(x-t) by ring, mul_comm] at mm
  exact mm

theorem slice_weight_thin_box (r t x : ℝ) (r3 : 3≤r) (t0 : 0<t) (t1 : t≤1/8)
    (d : 1≤4*r*t^2) (tx : t≤x) (xx : x≤t+1/(4*r*t)) :
    Real.exp (-3)*sliceWeight r t ≤ sliceWeight r x := by
  let w := 1/(4*r*t)
  have rp : 0<r := by linarith
  have w0 : 0<w := by dsimp [w]; positivity
  have w1 : w≤t := by
    apply (div_le_iff₀ (by positivity : 0<4*r*t)).2
    nlinarith only [d]
  have hw : 4*r*t*w=1 := by dsimp [w]; field_simp [rp.ne',t0.ne']
  have tw : t*w=1/(4*r) := by
    apply (eq_div_iff (by positivity : 4*r≠0)).2
    nlinarith only [hw]
  have xb := pow_le_pow_left₀ (t0.le.trans tx) xx 2
  have ww := mul_le_mul_of_nonneg_right w1 w0.le
  have tb : 1/2≤1-t^2 := by nlinarith only [pow_le_pow_left₀ t0.le t1 2]
  have tp : 0<1-t^2 := (by norm_num : (0:ℝ)<1/2).trans_le tb
  let s := 3/(2*r)
  have s0 : 0≤s := by dsimp [s]; positivity
  have s2 : s≤1/2 := (div_le_iff₀ (by positivity : 0<2*r)).2 (by linarith only [r3])
  have bb : x^2-t^2≤s/2 := by
    change x^2≤(t+w)^2 at xb
    have a : 3*t*w=s/2 := by rw [mul_assoc,tw]; dsimp [s]; ring
    nlinarith only [xb,ww,a]
  have low : 1-s≤(1-x^2)/(1-t^2) := by
    apply (le_div_iff₀ tp).2
    have h := mul_le_mul_of_nonneg_left tb s0
    nlinarith only [bb,h]
  have pos : 0<(1-x^2)/(1-t^2) := (show 0<1-s by linarith only [s2]).trans_le low
  have Q := one_sub_weight_rpow ((1-x^2)/(1-t^2)) s r s0 s2 rp.le low
  have QQ := mul_le_mul_of_nonneg_left Q (Real.rpow_nonneg tp.le r)
  rw [←Real.mul_rpow tp.le pos.le,
    show (1-t^2)*((1-x^2)/(1-t^2))=1-x^2 from by field_simp [tp.ne'],
    show -2*r*s=(-3:ℝ) from by dsimp [s]; field_simp [rp.ne'],
    mul_comm] at QQ
  exact QQ

theorem slice_weight_shift_upper (r t s : ℝ) (r0 : 0≤r) (t0 : 0<t) (t1 : t≤1/8)
    (s0 : 0≤s) (st : s≤t) :
    sliceWeight r (t-s) ≤ Real.exp (4*r*t*s)*sliceWeight r t := by
  have tB : 1/2≤1-t^2 := by nlinarith only [pow_le_pow_left₀ t0.le t1 2]
  have tp : 0<1-t^2 := (by norm_num : (0:ℝ)<1/2).trans_le tB
  have d := pow_le_pow_left₀ (sub_nonneg.mpr st) (by linarith only [s0] : t-s≤t) 2
  have xp : 0<1-(t-s)^2 := by linarith only [tp,d]
  let q := (1-(t-s)^2)/(1-t^2)
  have qp : 0<q := div_pos xp tp
  have qhi : q≤1+4*t*s := by
    apply (div_le_iff₀ tp).2
    have b := mul_le_mul_of_nonneg_left tB (show 0≤4*t*s by positivity)
    nlinarith only [b,sq_nonneg s]
  have ll := Real.log_le_sub_one_of_pos qp
  have le : q^r≤Real.exp (4*r*t*s) := by
    rw [Real.rpow_def_of_pos qp]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (show Real.log q≤4*t*s by linarith only [ll,qhi]) r0
    nlinarith only [h]
  have eq : (1-t^2)*q=1-(t-s)^2 := by dsimp [q]; field_simp [tp.ne']
  unfold sliceWeight
  rw [←eq,Real.mul_rpow tp.le qp.le,mul_comm (Real.exp _) _]
  exact mul_le_mul_of_nonneg_left le (Real.rpow_nonneg tp.le _)

#print axioms slice_weight_upper_exp
#print axioms slice_weight_thin_box
end RobustFolkman.GeometricGap
