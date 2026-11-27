import GeometricFailurePowers
import Mathlib.Data.Nat.Choose.Basic

namespace RobustFolkman.GeometricGap

theorem choose_three_cubic (n : ℕ) (n4 : 4≤n) :
    (n:ℝ)^3/48 ≤ (n.choose 3:ℝ) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose n 3
  norm_num [Nat.descFactorial_succ] at h
  have a : (n:ℝ)-1 = (↑(n-1):ℝ) := by simpa using (Nat.cast_sub (R:=ℝ) (by omega : 1≤n)).symm
  have b : (n:ℝ)-2 = (↑(n-2):ℝ) := by simpa using (Nat.cast_sub (R:=ℝ) (by omega : 2≤n)).symm
  have e : (n:ℝ)*((n:ℝ)-1)*((n:ℝ)-2) = 6*(n.choose 3:ℝ) := by
    rw [a,b]
    exact_mod_cast (by simpa [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using h : n*(n-1)*(n-2)=6*n.choose 3)
  have nR : (4:ℝ)≤n := by exact_mod_cast n4
  have l1 : (n:ℝ)/2≤(n:ℝ)-1 := by linarith
  have l2 : (n:ℝ)/2≤(n:ℝ)-2 := by linarith
  have m : ((n:ℝ)/2)*((n:ℝ)/2)≤((n:ℝ)-1)*((n:ℝ)-2) :=
    mul_le_mul l1 l2 (by positivity) (by linarith)
  have p := mul_le_mul_of_nonneg_left m (show 0≤(n:ℝ) by positivity)
  nlinarith only [e,p]

/-- Explicit reduction of the Chebyshev and Markov errors to the four
powers of the sample size controlled by the strict rate window. -/
theorem moment_error_from_four (n : ℕ) (n4 : 4≤n) (a u v h j q : ℝ)
    (a0 : 0<a) (u0 : 0<u) (v0 : 0≤v) (h0 : 0≤h) (j0 : 0≤j) (q0 : 0≤q)
    (T : 1/((n:ℝ)^3*u)≤q) (D : v/((n:ℝ)^2*u^2)≤q)
    (H : (n:ℝ)^2*h/u≤q) (J : (n:ℝ)^3*j/u≤q) :
    let C := (n.choose 3:ℝ)
    let μ := C*u
    4/μ^2 * (C*(u+(↑(3*(n-3)) : ℝ)*v)) +
      2/(a*μ) * (3*(n:ℝ)^5*h+(n:ℝ)^6*j) ≤ (768+384/a)*q := by
  intro C μ
  let N : ℝ := n
  have N0 : 0<N := by dsimp [N]; positivity
  have l : N^3/48≤C := choose_three_cubic n n4
  have C0 : 0<C := (div_pos (pow_pos N0 _) (by norm_num)).trans_le l
  have x : (↑(3*(n-3)):ℝ) ≤ 3*N := by
    rw [Nat.cast_mul,Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_left (by dsimp [N]; exact_mod_cast Nat.sub_le n 3) (by norm_num)
  have P := (div_le_iff₀ (mul_pos (pow_pos N0 _) u0)).mp T
  have Q := (div_le_iff₀ (mul_pos (pow_pos N0 _) (pow_pos u0 _))).mp D
  have HR := (div_le_iff₀ u0).mp H
  have JR := (div_le_iff₀ u0).mp J
  have v1 : (↑(3*(n-3)):ℝ)*v ≤ 3*N*v := mul_le_mul_of_nonneg_right x v0
  have c : N^3≤48*C := by linarith only [l]
  have cv := mul_le_mul_of_nonneg_left Q (by positivity : 0≤3*N)
  have vari : u+(↑(3*(n-3)):ℝ)*v ≤ 192*q*C*u^2 := by
    have tpart := mul_le_mul_of_nonneg_right P u0.le
    have cpart := mul_le_mul_of_nonneg_right c (mul_nonneg q0 (sq_nonneg u))
    nlinarith only [tpart,cv,cpart,v1]
  have cvb : 4/μ^2*(C*(u+(↑(3*(n-3)):ℝ)*v))≤768*q := by
    dsimp [μ]
    have divp : 0<(C*u)^2 := pow_pos (mul_pos C0 u0) _
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ divp).mpr
    have m := mul_le_mul_of_nonneg_left vari (show 0≤4*C by positivity)
    nlinarith only [m]
  have ch1 := mul_le_mul_of_nonneg_left HR (by positivity : 0≤3*N^3)
  have ch2 := mul_le_mul_of_nonneg_left JR (by positivity : 0≤N^3)
  have ch3 := mul_le_mul_of_nonneg_right c (mul_nonneg q0 u0.le)
  have charge : 3*N^5*h+N^6*j≤192*C*q*u := by
    nlinarith only [ch1,ch2,ch3]
  have chb : 2/(a*μ)*(3*(n:ℝ)^5*h+(n:ℝ)^6*j)≤(384/a)*q := by
    dsimp [μ]
    change 2/(a*(C*u))*(3*N^5*h+N^6*j)≤(384/a)*q
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (mul_pos a0 (mul_pos C0 u0))).mpr
    have ha : (384/a)*q*(a*(C*u))=384*C*q*u := by field_simp
    rw [ha]
    linarith only [charge]
  nlinarith only [cvb,chb]

#print axioms choose_three_cubic
#print axioms moment_error_from_four
end RobustFolkman.GeometricGap
