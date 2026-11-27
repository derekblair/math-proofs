import GeometricAnchorBox
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace RobustFolkman.GeometricGap
open Finset Matrix Equiv
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem determinant_small_lower (M : Matrix I I ℝ) (t : ℝ) (t0 : 0≤t) (t1 : t≤1)
    (diag : ∀ i, M i i=1) (off : ∀ i j, i≠j → |M i j|≤t) :
    1-((Fintype.card (Perm I)-1 : ℕ) : ℝ)*t^2 ≤ M.det := by
  classical
  let term (p : Perm I) : ℝ :=
    ((Equiv.Perm.sign p : ℤ) : ℝ)*(∏ i, M (p i) i)
  have ident : term 1=1 := by simp [term,diag]
  have lower (p : Perm I) (ne : p≠1) : -t^2≤term p := by
    have P : ∏ i, M (p i) i = ∏ i∈p.support, M (p i) i := by
      rw [←Finset.prod_mul_prod_compl p.support (fun i => M (p i) i)]
      have unit : ∏ i∈p.supportᶜ, M (p i) i=1 := by
        apply Finset.prod_eq_one
        intro i hi
        rw [Equiv.Perm.notMem_support.mp (mem_compl.mp hi),diag]
      rw [unit,mul_one]
    have H : |∏ i, M (p i) i|≤t^2 := by
      rw [P,Finset.abs_prod]
      have A : ∏ i∈p.support, |M (p i) i| ≤ ∏ _i∈p.support, t := by
        apply Finset.prod_le_prod₀
        · exact fun _ _ => abs_nonneg _
        · intro i hi
          exact off _ _ (Equiv.Perm.mem_support.mp hi)
      have C : t^p.support.card≤t^2 :=
        pow_le_pow_of_le_one t0 t1 (Equiv.Perm.two_le_card_support_of_ne_one ne)
      exact A.trans ((by simpa only [Finset.prod_const] using C))
    unfold term
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with a|a
    · simpa [a] using (abs_le.mp H).1
    · have u := (abs_le.mp H).2
      simpa [a] using (neg_le_neg u)
  have det : M.det=∑ p,term p := Matrix.det_apply' M
  rw [det,←Finset.sum_erase_add _ term (mem_univ (1:Perm I)),ident]
  have h : ∑ p ∈ (univ : Finset (Perm I)).erase 1, (-t^2) ≤
      ∑ p ∈ (univ : Finset (Perm I)).erase 1, term p :=
    sum_le_sum fun p hp => lower p (ne_of_mem_erase hp)
  simp only [sum_const,nsmul_eq_mul,card_erase_of_mem (mem_univ (1:Perm I)),card_univ] at h
  linarith only [h]

theorem determinant_six_lower (M : Matrix I I ℝ) (t : ℝ) (t0 : 0≤t) (t1 : t≤1)
    (n : Fintype.card I≤6) (diag : ∀ i, M i i=1) (off : ∀ i j, i≠j → |M i j|≤t) :
    1-719*t^2≤M.det := by
  have k : Fintype.card (Perm I)≤720 := by
    rw [Fintype.card_perm]
    exact (Nat.factorial_le n).trans (by decide)
  have h : ((Fintype.card (Perm I)-1 : ℕ) : ℝ)≤719 := by exact_mod_cast (show Fintype.card (Perm I)-1≤719 by omega)
  have e := mul_le_mul_of_nonneg_right h (sq_nonneg t)
  linarith only [e,determinant_small_lower M t t0 t1 diag off]

#print axioms determinant_six_lower
end RobustFolkman.GeometricGap
