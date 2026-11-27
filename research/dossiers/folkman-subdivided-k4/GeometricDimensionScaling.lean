import GeometricActualRate
import Mathlib.Algebra.Order.Floor.Semiring

namespace RobustFolkman.GeometricGap
open MeasureTheory Matrix
open scoped ENNReal

noncomputable def graphDimension (X N : ℝ) : ℕ := ⌈Real.log N/X⌉₊

theorem graphDimension_residual (X N : ℝ) (Xp : 0<X) (Np : 1≤N) (k : ℕ)
    (L : (k:ℝ)+1≤Real.log N/X) :
    let d := graphDimension X N
    let m := d-(k+1)
    d = k+m+1 ∧
      |(m:ℝ)-Real.log N/X|≤(k:ℝ)+1 := by
  intro d m
  have a := Nat.le_ceil (Real.log N/X)
  have b := Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg Np) Xp.le)
  change Real.log N/X≤(d:ℝ) at a
  change (d:ℝ)<Real.log N/X+1 at b
  have l : k+1≤d := by exact_mod_cast L.trans a
  have dd : d=k+m+1 := by dsimp [m]; omega
  have dc : (d:ℝ)=(k:ℝ)+(m:ℝ)+1 := by exact_mod_cast dd
  refine ⟨dd,abs_le.mpr ⟨?_,?_⟩⟩ <;> linarith only [a,b,dc]

theorem scaled_rate_error (R X N A t : ℝ) (Xp : 0<X) (N1 : 1≤N)
    (m : ℕ) (t0 : 0<t) (am : |(m:ℝ)-Real.log N/X|≤A)
    (last : A*(|R|+t)≤t*(Real.log N/X))
    (p : ℝ) (p0 : 0<p)
    (err : |Real.log p/(m:ℝ)-R|≤t) (m0 : 0<m) :
    |Real.log p-Real.log N*(R/X)|≤(3*t/X)*Real.log N := by
  have m0' : 0<(m:ℝ) := by exact_mod_cast m0
  let l := Real.log N/X
  have lp : 0≤l := div_nonneg (Real.log_nonneg N1) Xp.le
  have mhi : (m:ℝ)≤l+A := by
    have f := (abs_le.mp am).2
    dsimp [l]
    linarith
  have absP : |Real.log p-(m:ℝ)*R|≤(m:ℝ)*t := by
    have e : Real.log p-(m:ℝ)*R=(Real.log p/(m:ℝ)-R)*(m:ℝ) := by
      field_simp
    rw [e,abs_mul,abs_of_pos m0',mul_comm (m:ℝ)]
    exact mul_le_mul_of_nonneg_right err m0'.le
  have er : Real.log p-Real.log N*(R/X) =
      (Real.log p-(m:ℝ)*R)+((m:ℝ)-l)*R := by
    dsimp [l]
    ring
  rw [er]
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  have h := mul_le_mul_of_nonneg_right am (abs_nonneg R)
  have h2 := mul_le_mul_of_nonneg_right mhi t0.le
  have d : (3*t/X)*Real.log N=3*t*l := by dsimp [l]; ring
  rw [d]
  change |(m:ℝ)-l|≤A at am
  change A*(|R|+t)≤t*l at last
  nlinarith only [absP,h,h2,last,mul_nonneg t0.le lp]

#print axioms graphDimension_residual
#print axioms scaled_rate_error
end RobustFolkman.GeometricGap
