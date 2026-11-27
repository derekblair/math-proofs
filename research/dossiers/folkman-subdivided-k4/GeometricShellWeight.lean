import GeometricTriangleShell
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace RobustFolkman.GeometricGap

theorem grain_corner_positive (t : ℝ) (t0 : 0≤t) (t1 : t≤1/4) :
    1/2 ≤ threeGramDet t t t ∧ threeGramDet t t t ≤ 1 := by
  have h : t^2≤(1/4:ℝ)^2 := pow_le_pow_left₀ t0 t1 2
  have w : 0≤t^3 := by positivity
  have w' := mul_nonneg (sq_nonneg t) (show 0≤3-2*t by linarith)
  unfold threeGramDet
  constructor <;> nlinarith only [h,w,w']

theorem triangle_shell_upper_weight (t x y z m : ℝ) (t0 : 0≤t) (t1 : t≤1/4) (m0 : 0<m)
    (x0 : 0≤x) (y0 : 0≤y) (z0 : 0≤z)
    (x1 : x≤1-t) (y1 : y≤1-t) (z1 : z≤1-t)
    (pd : 0≤threeGramDet (t+x) (t+y) (t+z)) :
    (threeGramDet (t+x) (t+y) (t+z) / threeGramDet t t t)^m ≤
      Real.exp (-m*t*(x+y+z)) := by
  let A := threeGramDet t t t
  let B := threeGramDet (t+x) (t+y) (t+z)
  have ⟨Alo,Ahi⟩ := grain_corner_positive t t0 t1
  have Ap : 0<A := by change 0<(threeGramDet t t t); linarith
  have h := triangle_det_corner_plane t x y z t0 t1 x0 y0 z0 x1 y1 z1
  have k : B/A≤1-t*(x+y+z) := by
    apply (div_le_iff₀ Ap).2
    have u := mul_le_mul_of_nonneg_right (show A≤2*(1-t) by dsimp [A]; linarith)
      (show 0≤t*(x+y+z) by positivity)
    dsimp [A,B] at *
    nlinarith only [h,u]
  have b0 : 0≤B/A := div_nonneg pd Ap.le
  rcases b0.eq_or_lt with eq|bp
  · rw [←eq,Real.zero_rpow m0.ne']; positivity
  · rw [Real.rpow_def_of_pos bp]
    apply Real.exp_le_exp.mpr
    have ll := Real.log_le_sub_one_of_pos bp
    have c := mul_le_mul_of_nonneg_right (show Real.log (B/A)≤ -t*(x+y+z) by
      linarith only [ll,k]) m0.le
    nlinarith only [c]

theorem triangle_shell_lower_weight (t x y z m : ℝ) (t0 : 0<t) (t1 : t≤1/4)
    (m36 : 36≤m) (dense : 1≤m*t^2) (x0 : 0≤x) (y0 : 0≤y) (z0 : 0≤z)
    (x1 : x≤1/(m*t)) (y1 : y≤1/(m*t)) (z1 : z≤1/(m*t)) :
    Real.exp (-36) ≤ (threeGramDet (t+x) (t+y) (t+z)/threeGramDet t t t)^m := by
  let w := 1/(m*t)
  let A := threeGramDet t t t
  let B := threeGramDet (t+x) (t+y) (t+z)
  have ⟨Alo,Ahi⟩ := grain_corner_positive t t0.le t1
  have Ap : 0<A := by change 0<(threeGramDet t t t); linarith
  have mp : 0<m := by linarith
  have w0 : 0<w := by dsimp [w]; positivity
  have w1 : w≤t := by
    apply (div_le_iff₀ (mul_pos mp t0)).2
    nlinarith only [dense]
  have mt : m*t*w=1 := by dsimp [w]; field_simp [ne_of_gt mp,ne_of_gt t0]
  have bw := triangle_det_corner_box_lower t x y z w t0.le (by linarith) x0 y0 z0 x1 y1 z1
  have sq := mul_le_mul_of_nonneg_right w1 w0.le
  have b9 : A-9/m≤B := by
    have e : t*w=1/m := by
      apply (eq_div_iff (ne_of_gt mp)).2
      nlinarith only [mt]
    dsimp [A,B]
    simp only [div_eq_mul_inv,one_mul] at e ⊢
    nlinarith only [bw,sq,e]
  have rr : 1-18/m≤B/A := by
    apply (le_div_iff₀ Ap).2
    have q := mul_le_mul_of_nonneg_left (show 1/2≤A from Alo) (show 0≤18/m by positivity)
    simp only [div_eq_mul_inv] at q b9 ⊢
    nlinarith only [q,b9]
  have z2 : 18/m≤1/2 := (div_le_iff₀ mp).2 (by linarith)
  have P : 0<B/A := (show 0<1-18/m by linarith).trans_le rr
  have I : (B/A)⁻¹≤1+36/m := by
    apply (inv_le_iff_one_le_mul₀ P).2
    have a := mul_le_mul_of_nonneg_right rr (show 0≤1+36/m by positivity)
    have b := mul_nonneg (show 0≤36/m by positivity) (show 0≤1/2-18/m by linarith)
    have eq : (1-18/m)*(1+36/m) = (1:ℝ)+(36/m)*(1/2-18/m) := by ring
    rw [eq] at a
    calc
      _ ≤ 1+(36/m)*(1/2-18/m) := by linarith only [b]
      _ ≤ (B/A)*(1+36/m) := a
      _ = _ := by ring
  have l : -(36/m)≤Real.log (B/A) := by
    linarith only [I,Real.one_sub_inv_le_log_of_pos P]
  rw [Real.rpow_def_of_pos P]
  apply Real.exp_le_exp.mpr
  have q := mul_le_mul_of_nonneg_right l mp.le
  have e : (-(36/m))*m = (-36:ℝ) := by field_simp [ne_of_gt mp]
  rwa [e] at q

#print axioms triangle_shell_upper_weight
#print axioms triangle_shell_lower_weight
end RobustFolkman.GeometricGap
