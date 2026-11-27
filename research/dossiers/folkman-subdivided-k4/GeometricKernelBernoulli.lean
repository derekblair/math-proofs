import GeometricKernelCovariance
import GeometricConditionalRowTail

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory Set Finset
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
variable {Ω I : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype I]

theorem bernoulli_feature_square_le (K : Ω→Ω→ℝ) (p : Ω→ℝ)
    (p0 : ∀ z, 0≤p z) (p1 : ∑ z,p z=1)
    (q θ : ℝ) (q0 : 0≤q)
    (bin : ∀ x y, K x y=0 ∨ K x y=1)
    (row : ∀ x, ∑ z,p z*K x z≤θ) (x : Ω) :
    ∑ z,(kernelFeature (fun x y => K x y-q) p x z)^2≤θ+q^2 := by
  have le (z) : (K x z-q)^2≤K x z+q^2 := by
    rcases bin x z with h|h
    · rw [h,zero_sub,neg_sq,zero_add]
    · rw [h,sub_sq]; linarith only [q0]
  calc
    _ = ∑ z, p z*(K x z-q)^2 := by
      apply Finset.sum_congr rfl
      intro z _
      rw [kernelFeature,mul_pow,Real.sq_sqrt (p0 z),mul_comm]
    _ ≤ ∑ z, p z*(K x z+q^2) := Finset.sum_le_sum fun z _ =>
      mul_le_mul_of_nonneg_left (le z) (p0 z)
    _ = (∑ z,p z*K x z)+q^2 := by
      simp only [mul_add,Finset.sum_add_distrib,←Finset.sum_mul,p1,one_mul]
    _ ≤ _ := add_le_add_left (row x) _

theorem bernoulli_column_square_le (K : Ω→Ω→ℝ) (bin : ∀ x y, K x y=0 ∨ K x y=1)
    (q : ℝ) (q0 : 0≤q) (x : I→Ω) (y : Ω) :
    ∑ i,(rightColumn (fun x y => K x y-q) x y i)^2≤
      (Fintype.card I:ℝ)*q^2 + (familyRetained (fun i => {z : Ω | K (x i) z=1}) y).card := by
  classical
  have pr (i : I) : K (x i) y=(if K (x i) y=1 then (1:ℝ) else 0) := by
    rcases bin (x i) y with h|h
    · simp [h]
    · simp [h]
  have h (i : I) : (K (x i) y-q)^2≤q^2+(if K (x i) y=1 then (1:ℝ) else 0) := by
    rw [←pr]
    rcases bin (x i) y with h|h
    · rw [h,zero_sub,neg_sq,add_zero]
    · rw [h,sub_sq]; linarith only [q0]
  calc
    _ ≤ ∑ i, (q^2+(if K (x i) y=1 then (1:ℝ) else 0)) :=
      Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Finset.card_univ,←Finset.sum_filter]
      simp [familyRetained]

#print axioms bernoulli_feature_square_le
#print axioms bernoulli_column_square_le
end RobustFolkman.GeometricGap
