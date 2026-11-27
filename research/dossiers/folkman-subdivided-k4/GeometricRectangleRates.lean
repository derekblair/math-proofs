import GeometricRectangleTail

namespace RobustFolkman.GeometricGap
open MeasureTheory Set RMT
open scoped ENNReal

theorem rectangle_first_stage_rate (D n L : ℕ) (h : n≤L)
    (q : ℝ) (qp : 0<q) (q1 : q≤1) (Lp : 0<L) :
    matrixBernsteinTailBound D ((n:ℝ)*(3*q)*(q/100)^2) (3*q+(q/100)^2) ((L:ℝ)*q^2/10000) ≤
      2*(D:ℝ)*Real.exp (-(L:ℝ)*q/1000000) := by
  have nL : (n:ℝ)≤L := by exact_mod_cast h
  have l : 0<(L:ℝ) := by exact_mod_cast Lp
  let S := (L:ℝ)*q^2/10000
  let den := (n:ℝ)*(3*q)*(q/100)^2 + (3*q+(q/100)^2)*S/3
  have d0 : 0<den := by dsimp [den,S]; positivity
  have d : den≤(L:ℝ)*q^3/1000 := by
    have a := mul_le_mul_of_nonneg_right nL (by positivity : 0≤(3*q)*(q/100)^2)
    have b : q^2≤q := by nlinarith only [mul_nonneg qp.le (sub_nonneg.mpr q1)]
    have c := mul_le_mul_of_nonneg_right (show 3*q+(q/100)^2≤4*q by nlinarith only [b,qp])
      (show 0≤S/3 by dsimp [S]; positivity)
    dsimp [den,S] at *
    nlinarith only [a,c,mul_pos l (show 0<q^3 by positivity)]
  unfold matrixBernsteinTailBound
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  change -(S^2/2)/den≤_
  rw [neg_div]
  have larger : 0<(L:ℝ)*q^3/1000 := by positivity
  have dl := div_le_div_of_nonneg_left (show 0≤S^2/2 by positivity) d0 d
  have exactb : (S^2/2)/((L:ℝ)*q^3/1000)=(L:ℝ)*q/200000 := by
    dsimp [S]
    field_simp
    ring
  rw [exactb] at dl
  linarith only [dl,mul_pos l qp]

theorem rectangle_second_stage_rate (n m L : ℕ) (hn : n≤L) (hm : m≤L)
    (q T B : ℝ) (qp : 0<q) (q1 : q≤1) (Lp : 0<L) (T0 : 0≤T) (Bp : 0<B)
    (TB : T≤(L:ℝ)*q^2/5000) (BB : B≤10*(L:ℝ)*q) :
    matrixBernsteinTailBound n ((m:ℝ)*B*T) (B+T) ((L:ℝ)^2*q^2/10000) ≤
      2*(L:ℝ)*Real.exp (-(L:ℝ)*q/1000000) := by
  have nL : (n:ℝ)≤L := by exact_mod_cast hn
  have mL : (m:ℝ)≤L := by exact_mod_cast hm
  have l : 0<(L:ℝ) := by exact_mod_cast Lp
  let U := (L:ℝ)^2*q^2/10000
  let den := (m:ℝ)*B*T+(B+T)*U/3
  have d0 : 0<den := by dsimp [den,U]; positivity
  have d : den≤(L:ℝ)^3*q^3/200 := by
    have h := mul_le_mul (mul_le_mul mL BB Bp.le l.le) TB T0 (by positivity)
    have b : q^2≤q := by nlinarith only [mul_nonneg qp.le (sub_nonneg.mpr q1)]
    have c := mul_le_mul_of_nonneg_left b (show 0≤(L:ℝ) by positivity)
    have j : B+T≤11*(L:ℝ)*q := by nlinarith only [TB,BB,c,mul_pos l qp]
    have jj := mul_le_mul_of_nonneg_right j (show 0≤U/3 by dsimp [U]; positivity)
    dsimp [den,U] at *
    nlinarith only [h,jj,mul_pos (show 0<(L:ℝ)^3 by positivity) (show 0<q^3 by positivity)]
  unfold matrixBernsteinTailBound
  apply mul_le_mul (by linarith only [nL]) (Real.exp_le_exp.2 ?_) (by positivity) (by positivity)
  change -(U^2/2)/den≤_
  rw [neg_div]
  have dl := div_le_div_of_nonneg_left (show 0≤U^2/2 by positivity) d0 d
  have exactb : (U^2/2)/((L:ℝ)^3*q^3/200)=(L:ℝ)*q/1000000 := by
    dsimp [U]
    field_simp
    ring
  rw [exactb] at dl
  linarith only [dl]

theorem rectangle_truncation_rate (n L k : ℕ) (h : n≤L)
    (q p : ℝ) (q0 : 0≤q) (p0 : 0≤p) (pB : p≤2*q) (kB : 8*(L:ℝ)*q≤k) :
    Real.exp (2*(n:ℝ)*p)/(2:ℝ)^k ≤ Real.exp (-(L:ℝ)*q) := by
  have nL : (n:ℝ)≤L := by exact_mod_cast h
  have pow : (2:ℝ)^k=Real.exp ((k:ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
  rw [pow,←Real.exp_sub]
  apply Real.exp_le_exp.2
  have a := mul_le_mul nL pB p0 (by positivity : 0≤(L:ℝ))
  have lo : (5/8:ℝ)≤Real.log 2 := by
    have a := Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<8/7 by norm_num)
    have b := Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<7/6 by norm_num)
    have c := Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<6/5 by norm_num)
    have d := Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<5/4 by norm_num)
    have e : Real.log (2:ℝ)=Real.log (8/7)+Real.log (7/6)+Real.log (6/5)+Real.log (5/4) := by
      rw [←Real.log_mul (by norm_num : (8/7:ℝ)≠0) (by norm_num : (7/6:ℝ)≠0),
        ←Real.log_mul (by norm_num : (8/7:ℝ)*(7/6)≠0) (by norm_num : (6/5:ℝ)≠0),
        ←Real.log_mul (by norm_num : (8/7:ℝ)*(7/6)*(6/5)≠0) (by norm_num : (5/4:ℝ)≠0)]
      congr 1
      norm_num
    norm_num at a b c d
    linarith only [a,b,c,d,e]
  have b := mul_le_mul kB lo (by norm_num : (0:ℝ)≤5/8) (by positivity : 0≤(k:ℝ))
  nlinarith only [a,b]

#print axioms rectangle_first_stage_rate
#print axioms rectangle_second_stage_rate
#print axioms rectangle_truncation_rate
end RobustFolkman.GeometricGap
