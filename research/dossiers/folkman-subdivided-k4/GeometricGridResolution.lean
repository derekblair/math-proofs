import GeometricGridRateLower
import GeometricQuantizedCap

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped ENNReal BigOperators

def gridResolution (n k : ℕ) : ℕ := 2^(k+4*n+12)

theorem gridResolution_pos (n k : ℕ) : 0<gridResolution n k := by
  unfold gridResolution
  positivity

theorem sqrt_grid_dimension (n : ℕ) : Real.sqrt ((n+3:ℕ):ℝ)≤4*(2:ℝ)^n := by
  have dim : ((n+3:ℕ):ℝ)≤4*(2:ℝ)^n := by
    induction n with
    | zero => norm_num
    | succ n h =>
      push_cast [Nat.succ_eq_add_one] at h ⊢
      rw [pow_succ]
      have hn : (0:ℝ)≤n := Nat.cast_nonneg n
      linarith only [h,hn]
  apply (Real.sqrt_le_iff).2 ⟨by positivity,?_⟩
  have pp : (1:ℝ)≤(2:ℝ)^n := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  have h : (4*(2:ℝ)^n) * 1 ≤ (4*(2:ℝ)^n)*(4*(2:ℝ)^n) :=
    mul_le_mul_of_nonneg_left (by linarith only [pp]) (by positivity)
  exact dim.trans (by simpa only [mul_one,pow_two] using h)

theorem grid_resolution_strip (n k : ℕ) (q Z : ℝ)
    (ql : 1/(8*(2:ℝ)^n)≤q) (Zl : 1/(4*(2:ℝ)^n)≤Z) :
    let m := gridResolution n k
    let δ := 2*(Real.sqrt ((n+3:ℕ):ℝ)/(m:ℝ))
    2*δ/Z≤(1/2:ℝ)^k*q^2 ∧ δ≤1/4 := by
  intro m δ
  let s : ℝ := (2:ℝ)^n
  let r : ℝ := (2:ℝ)^k
  have sp : 0<s := by dsimp [s]; positivity
  have rp : 0<r := by dsimp [r]; positivity
  have s1 : 1≤s := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  have r1 : 1≤r := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  have mp : 0<(m:ℝ) := by exact_mod_cast gridResolution_pos n k
  have Zp : 0<Z := (by positivity : 0<1/(4*(2:ℝ)^n)).trans_le Zl
  have mr : (m:ℝ)=4096*r*s^4 := by
    dsimp [m,gridResolution,s,r]
    push_cast
    rw [pow_add,pow_add,mul_comm 4 n,pow_mul]
    norm_num
    ring
  have ci : (1/2:ℝ)^k=1/r := by dsimp [r]; rw [div_pow,one_pow]
  have δb : δ≤(8*s)/(m:ℝ) := by
    dsimp [δ]
    rw [←mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith only [sqrt_grid_dimension n]) mp.le
  have zi : 1/Z≤4*s := by
    have a : 0<4*s := by positivity
    apply (div_le_iff₀ Zp).2
    have h := (div_le_iff₀ a).1 Zl
    simpa only [mul_comm] using h
  have qp : 0≤q := (by positivity : 0≤1/(8*(2:ℝ)^n)).trans ql
  have first : 2*δ/Z≤(1/2:ℝ)^k*q^2 := by
    calc
      _ = (2*δ)*(1/Z) := by ring
      _ ≤ (2*((8*s)/(m:ℝ)))*(4*s) := mul_le_mul
        (mul_le_mul_of_nonneg_left δb (by norm_num)) zi (by positivity) (by positivity)
      _ = (1/2:ℝ)^k*(1/(8*s))^2 := by rw [mr,ci]; field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ql 2) (by positivity)
  refine ⟨first,δb.trans ?_⟩
  apply (div_le_iff₀ mp).2
  rw [mr]
  have sx : s≤s^4 := by
    have h : s*1≤s*s^3 := mul_le_mul_of_nonneg_left (one_le_pow₀ s1) sp.le
    simpa [pow_succ',mul_comm] using h
  have rx : s^4≤r*s^4 := by simpa only [one_mul] using mul_le_mul_of_nonneg_right r1 (pow_nonneg sp.le 4)
  nlinarith only [sx,rx,sp.le]

theorem grid_log_card_bound (n k : ℕ) :
    Real.log (Fintype.card (GridCode (n+3) (gridResolution n k)):ℝ) ≤
      ((n+3:ℕ):ℝ)*((k+4*n+14:ℕ):ℝ)*Real.log 2 := by
  let m := gridResolution n k
  have mp : 0<(m:ℝ) := by exact_mod_cast gridResolution_pos n k
  have m1 : 1≤(m:ℝ) := by exact_mod_cast gridResolution_pos n k
  have eq : (Fintype.card (GridCode (n+3) m):ℝ)=(2*(m:ℝ)+1)^(n+3) := by
    simp [GridCode,Fintype.card_fun]
  change Real.log (Fintype.card (GridCode (n+3) m):ℝ)≤_
  rw [eq,Real.log_pow]
  have h : Real.log (2*(m:ℝ)+1) ≤ Real.log (4*(m:ℝ)) :=
    Real.log_le_log (by positivity) (by linarith only [m1])
  have he : Real.log (4*(m:ℝ))=((k+4*n+14:ℕ):ℝ)*Real.log 2 := by
    have hpow : 4*(m:ℝ)=(2:ℝ)^(k+4*n+14) := by
      dsimp [m,gridResolution]
      push_cast
      rw [show k+4*n+14=(k+4*n+12)+2 by omega,pow_add]
      norm_num
      ring
    rw [hpow,Real.log_pow]
  rw [he] at h
  calc
    _ ≤ ((n+3:ℕ):ℝ) * (((k+4*n+14:ℕ):ℝ)*Real.log 2) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

#print axioms grid_resolution_strip
#print axioms grid_log_card_bound
end RobustFolkman.GeometricGap
