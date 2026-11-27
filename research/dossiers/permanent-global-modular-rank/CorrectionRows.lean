import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Tactic

open scoped BigOperators
open Finset

namespace PermanentCorrection
variable {I R : Type*} [DecidableEq I] [Fintype I] [CommSemiring R]

def rowMix (B C : Matrix I I R) (s : I → Bool) : Matrix I I R :=
  Matrix.of (fun i j => if s i then C i j else B i j)

theorem permanent_row_order (M : Matrix I I R) :
    M.permanent = ∑ σ : Equiv.Perm I, ∏ i, M i (σ i) := by
  rw [← Matrix.permanent_transpose M]
  simp [Matrix.permanent]

theorem rowCorrectionExpansion (B C : Matrix I I R) (p : R) :
    (B + p • C).permanent =
    ∑ s : I → Bool,
      p ^ (Finset.univ.filter fun i => s i = true).card * (rowMix B C s).permanent := by
  classical
  simp only [permanent_row_order]
  calc
    _ = ∑ σ : Equiv.Perm I, ∑ s : I → Bool,
        ∏ i, (if s i then p * C i (σ i) else B i (σ i)) := by
      apply Finset.sum_congr rfl
      intro σ _
      simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fintype.sum_bool,
        ite_true, Bool.false_eq_true, if_false, add_comm, Fintype.piFinset_univ]
        using (Finset.prod_univ_sum (fun _ : I => (Finset.univ : Finset Bool))
          (fun i v => if v then p * C i (σ i) else B i (σ i)))
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      have hh : (∏ i : I, if s i then p else 1) =
          p ^ (Finset.univ.filter fun i => s i = true).card := by
        rw [← Finset.prod_filter]
        simp
      rw [← hh, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      cases h : s i <;> simp [rowMix, h]

#print axioms rowCorrectionExpansion
end PermanentCorrection
