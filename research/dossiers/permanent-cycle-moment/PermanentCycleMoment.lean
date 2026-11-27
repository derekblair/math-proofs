import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace PermanentCycleMoment

theorem weighted_symmetric_pair_bound {ι : Type*} [Fintype ι]
    (a : ι → ι → ℝ) (x : ι → ℝ) (c : ℝ)
    (ha : ∀ i j, 0 ≤ a i j) (hs : ∀ i j, a i j = a j i)
    (hx : ∀ i, 0 ≤ x i) (hn : ∑ i, x i ^ 2 = 1)
    (hr : ∀ i, ∑ j, a i j * (x i * x j) ≤ c) :
    ∑ i, ∑ j, a i j * (x i ^ 2 * x j ^ 2) ≤ c := by
  let b : ι → ι → ℝ := fun i j => a i j * (x i * x j) * x i ^ 2
  have hpair (i j : ι) :
      a i j * (x i ^ 2 * x j ^ 2) ≤ (b i j + b j i) / 2 := by
    have hm := mul_nonneg (mul_nonneg (ha i j) (mul_nonneg (hx i) (hx j)))
      (sq_nonneg (x i - x j))
    dsimp [b]
    rw [← hs i j]
    nlinarith
  have hswap : (∑ i, ∑ j, b j i) = (∑ i, ∑ j, b i j) := by
    rw [Finset.sum_comm]
  calc
    (∑ i, ∑ j, a i j * (x i ^ 2 * x j ^ 2)) ≤
        ∑ i, ∑ j, (b i j + b j i) / 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
    _ = ∑ i, ∑ j, b i j := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib]
      rw [hswap]
      ring
    _ = ∑ i, (∑ j, a i j * (x i * x j)) * x i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul]
    _ ≤ ∑ i, c * x i ^ 2 :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hr i) (sq_nonneg _)
    _ = c := by rw [← Finset.mul_sum, hn, mul_one]

theorem complementary_square_sum {ι : Type*} [Fintype ι]
    (e : ι ≃ ι) (h : ι → ℝ) :
    (∑ i, h i * h (e i)) ≤ ∑ i, h i ^ 2 := by
  have hswap : (∑ i, h (e i) ^ 2) = ∑ i, h i ^ 2 :=
    Equiv.sum_comp e (fun i => h i ^ 2)
  calc
    (∑ i, h i * h (e i)) ≤ ∑ i, (h i ^ 2 + h (e i) ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro i hi
      nlinarith [sq_nonneg (h i - h (e i))]
    _ = _ := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib]
      rw [hswap]
      ring

theorem threshold_constants : (35 : ℝ)^7 < 2 * 32^7 ∧ (3 : ℝ)^3 < 2^5 := by
  norm_num

theorem pivot_constants :
    (349 / 250 : ℚ)^3 ≥ 2 * ((907 / 1000) * (349 / 250) + (93 / 1000)) ∧
    (1699 / 1000 : ℚ)^3 ≥ 3 * ((907 / 1000) * (1699 / 1000) + (93 / 1000)) := by
  norm_num

set_option maxRecDepth 4096 in
set_option exponentiation.threshold 1024 in
theorem tail_integer_certificate : 14^94 * 54^1000 < (2 : ℕ)^500 * 49^1000 := by
  norm_num

end PermanentCycleMoment

#print axioms PermanentCycleMoment.weighted_symmetric_pair_bound
#print axioms PermanentCycleMoment.complementary_square_sum
#print axioms PermanentCycleMoment.pivot_constants
#print axioms PermanentCycleMoment.tail_integer_certificate
