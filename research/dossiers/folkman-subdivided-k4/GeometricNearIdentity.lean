import GeometricSchurLocal
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Basic.Real.Star
import Mathlib.Tactic.Positivity

namespace RobustFolkman.GeometricGap
open Finset Matrix
variable {K I : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Fintype I] [DecidableEq I]

theorem near_identity_quadratic (A : Matrix I I K) (ε : K) (e0 : 0≤ε)
    (diff : ∀ i j, |A i j - (1 : Matrix I I K) i j| ≤ ε) (v : I → K) :
    (1-ε*(Fintype.card I : K))*(∑ i, (v i)^2) ≤ A.toBilin' v v := by
  let R : Matrix I I K := A-1
  have entry (i j : I) :
      -(ε*(v i ^ 2+v j ^ 2)/2) ≤ v i * R i j * v j := by
    have e : |R i j|≤ε := diff i j
    have ap : |v i| * |v j| ≤ (v i ^ 2+v j ^ 2)/2 := by
      have h := sq_nonneg (|v i| - |v j|)
      rw [sub_sq, sq_abs, sq_abs] at h
      linarith only [h]
    have g : |v i * R i j * v j| ≤ ε*(v i ^ 2+v j ^ 2)/2 := by
      rw [abs_mul,abs_mul]
      calc
        _ ≤ |v i| * ε * |v j| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e (abs_nonneg _)) (abs_nonneg _)
        _ ≤ _ := calc
          _ = ε*(|v i| * |v j|) := by ring
          _ ≤ ε*((v i ^ 2+v j ^ 2)/2) := mul_le_mul_of_nonneg_left ap e0
          _ = _ := by ring
    exact (abs_le.mp g).1
  have sum_edge :
      (∑ i : I, ∑ j : I, -(ε*(v i ^ 2+v j ^ 2)/2)) ≤
        ∑ i : I, ∑ j : I, v i * R i j * v j := by
    apply sum_le_sum
    intro i _
    apply sum_le_sum
    intro j _
    exact entry i j
  have total : (∑ i : I, ∑ j : I, -(ε*(v i ^ 2+v j ^ 2)/2)) =
      -(ε*(Fintype.card I : K))*(∑ i : I, (v i)^2) := by
    have e1 : (∑ i : I, ∑ _j : I, v i ^ 2) = (Fintype.card I : K)*(∑ i : I, v i^2) := by
      simp [Finset.mul_sum]
    have e2 : (∑ _i : I, ∑ j : I, v j ^ 2) = (Fintype.card I : K)*(∑ i : I, v i^2) := by simp
    calc
      _ = -(ε/2)*((∑ i : I, ∑ _j : I, v i ^ 2)+(∑ _i : I, ∑ j : I, v j ^ 2)) := by
        rw [←Finset.sum_add_distrib]
        simp only [Finset.mul_sum, ←Finset.sum_add_distrib]
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [e1,e2]; ring
  rw [total] at sum_edge
  have form : A.toBilin' v v=(∑ i, (v i)^2)+(∑ i : I, ∑ j : I, v i * R i j * v j) := by
    rw [Matrix.toBilin'_apply']
    have hA : A=1+R := by unfold R; abel
    nth_rw 1 [hA]
    rw [Matrix.add_mulVec,Matrix.one_mulVec,dotProduct_add]
    congr 1
    · simp [dotProduct,pow_two]
    · exact (Matrix.toBilin'_apply' R v v).symm.trans (Matrix.toBilin'_apply R v v)
  rw [form]
  linarith only [sum_edge]

theorem near_identity_positive (A : Matrix I I K) (ε : K) (e0 : 0≤ε)
    (radius : ε*(Fintype.card I : K)<1)
    (diff : ∀ i j, |A i j - (1 : Matrix I I K) i j| ≤ ε)
    (v : I→K) (v0 : v≠0) : 0<A.toBilin' v v := by
  have some : ∃ i, v i ≠ 0 := by
    by_contra! no
    exact v0 (funext no)
  obtain ⟨i,hi⟩ := some
  have mass : 0 < (∑ k, v k ^ 2) :=
    (sq_pos_of_ne_zero hi).trans_le
      (Finset.single_le_sum (fun k _ => sq_nonneg (v k)) (mem_univ i))
  exact (mul_pos (sub_pos.mpr radius) mass).trans_le (near_identity_quadratic A ε e0 diff v)

theorem near_identity_pd (A : Matrix I I ℝ) (sym : A.IsHermitian) (ε : ℝ) (e0 : 0≤ε)
    (radius : ε*(Fintype.card I : ℝ)<1)
    (diff : ∀ i j, |A i j - (1 : Matrix I I ℝ) i j| ≤ ε) : A.PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨sym,?_⟩
  intro v v0
  simpa [Matrix.toBilin'_apply'] using near_identity_positive A ε e0 radius diff v v0

#print axioms near_identity_pd
end RobustFolkman.GeometricGap
