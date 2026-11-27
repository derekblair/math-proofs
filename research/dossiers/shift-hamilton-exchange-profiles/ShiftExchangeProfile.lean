import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace ShiftExchangeProfile

theorem winding_options {m w : ℕ} (hm : 2 ≤ m) (hw : 0 < w)
    (h : w*m ≤ 2*m+1) : w = 1 ∨ w = 2 := by
  by_contra! hh
  have h₀ : 3 ≤ w := by omega
  have h₁ := Nat.mul_le_mul_right m h₀
  omega

theorem no_slack_saturates {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (step : ι → ℕ) (s : ℕ)
    (hcap : ∀ i ∈ A, step i ≤ s)
    (h : ∑ i ∈ A, step i = A.card*s) :
    ∀ i ∈ A, step i = s := by
  intro i hi
  have hsum : ∑ j ∈ A.erase i, step j ≤ ∑ j ∈ A.erase i, s :=
    Finset.sum_le_sum fun j hj => hcap j (Finset.mem_of_mem_erase hj)
  have hsum' : (∑ j ∈ A.erase i, step j) ≤ (A.erase i).card * s := by
    simpa only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id] using hsum
  have heu := Finset.sum_erase_add A step hi
  rw [h] at heu
  have hcard : (A.erase i).card + 1 = A.card := Finset.card_erase_add_one hi
  rw [← hcard, Nat.add_mul, one_mul] at heu
  have hh := hcap i hi
  clear hsum
  omega

theorem interleave_two_runs (j b : ℤ) (hb : 0 < b) :
    j*(2*b+1)-b-1 < j*(2*b+1)-1 ∧
    j*(2*b+1)-1 < (j+1)*(2*b+1)-b-1 := by
  constructor
  · omega
  · have he : (j+1)*(2*b+1) = j*(2*b+1)+(2*b+1) := by ring
    rw [he]
    omega

theorem arithmetic_boundary (g j w : ℤ) (h : j*w = 2) :
    g-j*(g*w) = -g := by
  calc
    g-j*(g*w) = g*(1-j*w) := by ring
    _ = -g := by rw [h]; ring

end ShiftExchangeProfile

#print axioms ShiftExchangeProfile.winding_options
#print axioms ShiftExchangeProfile.no_slack_saturates
#print axioms ShiftExchangeProfile.interleave_two_runs
#print axioms ShiftExchangeProfile.arithmetic_boundary
