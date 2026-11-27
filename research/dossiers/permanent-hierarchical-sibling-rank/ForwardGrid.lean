import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Tactic

open scoped BigOperators fwdDiff
open Finset

namespace PermanentGrid

variable {R : Type*} [CommRing R]

/-- The forward-difference contribution of one coordinate on a monomial. -/
noncomputable def deltaPower (order exponent : ℕ) : R :=
  ((Δ_[1]^[order] (fun x : R => x ^ exponent)) 0)

/-- Contribution of the tensor-product difference grid to a single monomial. -/
noncomputable def gridMonomial {ι : Type} [Fintype ι] (a b : ι → ℕ) : R :=
  ∏ i, deltaPower (a i) (b i)

theorem deltaPower_zero {n k : ℕ} (h : k < n) :
    deltaPower (R := R) n k = 0 := by
  unfold deltaPower
  rw [fwdDiff_iter_pow_eq_zero_of_lt h]
  rfl

theorem deltaPower_diagonal (n : ℕ) :
    deltaPower n n = (n.factorial : R) := by
  unfold deltaPower
  rw [fwdDiff_iter_eq_factorial]
  rfl

theorem deltaPower_grid (n k : ℕ) :
    deltaPower n k =
      ∑ j ∈ Finset.range (n + 1), ((-1 : ℤ) ^ (n - j) * (n.choose j : ℤ)) • ((j : R) ^ k) := by
  unfold deltaPower
  rw [fwdDiff_iter_eq_sum_shift]
  simp

/-- The Cartesian grid implementation of the tensor-product difference. -/
theorem gridMonomial_explicit {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ι → ℕ) :
    gridMonomial a b =
      ∑ x ∈ Fintype.piFinset (fun i => Finset.range (a i + 1)),
        ∏ i, ((-1 : ℤ) ^ (a i - x i) * ((a i).choose (x i) : ℤ)) • ((x i : R) ^ (b i)) := by
  classical
  simp only [gridMonomial, deltaPower_grid]
  exact Finset.prod_univ_sum _ _

/-- Exact mixed difference at a fixed homogeneous degree. -/
theorem extractMonomial {ι : Type} [Fintype ι] (a b : ι → ℕ)
    (hdeg : ∑ i, a i = ∑ i, b i) :
    gridMonomial a b = if a = b then ∏ i, ( (a i).factorial : R) else 0 := by
  classical
  by_cases h : a = b
  · subst b
    simp [gridMonomial, deltaPower_diagonal]
  · simp [h, gridMonomial]
    have H : ∃ i, b i < a i := by
      by_contra hh
      push Not at hh
      have hneq : ∃ i, a i ≠ b i := by
        by_contra hn
        push Not at hn
        exact h (funext hn)
      obtain ⟨i, hi⟩ := hneq
      have hs : ∑ i, a i < ∑ i, b i :=
        Finset.sum_lt_sum (fun j _ => hh j) ⟨i, Finset.mem_univ i, lt_of_le_of_ne (hh i) hi⟩
      exact (ne_of_lt hs) hdeg
    obtain ⟨i, hi⟩ := H
    exact Finset.prod_eq_zero (Finset.mem_univ i) (deltaPower_zero hi)

/-- Linear coefficient isolation for a finite list of homogeneous monomials,
allowing repeated exponent vectors. -/
theorem extractHomogeneous {ι κ : Type} [Fintype ι]
    (S : Finset κ) (a : ι → ℕ) (b : κ → ι → ℕ) (c : κ → R)
    (hdeg : ∀ k ∈ S, ∑ i, a i = ∑ i, b k i) :
    ∑ k ∈ S, c k * gridMonomial a (b k) =
    (∏ i, ((a i).factorial : R)) * ∑ k ∈ S, (if b k = a then c k else 0) := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [extractMonomial a (b k) (hdeg k hk)]
  by_cases heq : b k = a
  · simp [heq, mul_comm]
  · simp [heq, Ne.symm heq]

#print axioms gridMonomial_explicit
#print axioms extractMonomial
#print axioms extractHomogeneous

end PermanentGrid
