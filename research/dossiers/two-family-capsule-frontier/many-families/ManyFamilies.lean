import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace ManyFamilies

def minLoss (n f M : ℕ) := f*(M/n)+min f (M%n)

/-- The only facts needed from sorting are that at least f entries
exceed q, or every tail entry is bounded by q. -/
theorem top_lower (n f q s L B : ℕ) (hf : f≤n)
    (total : L+B=n*q+s)
    (split : f*(q+1)≤L ∨ B≤(n-f)*q) :
    f*q+min f s≤L := by
  rcases split with large|small
  · rw [Nat.mul_succ] at large
    have h := Nat.min_le_left f s
    omega
  · have parts : f*q+(n-f)*q=n*q := by
      rw [←Nat.add_mul]
      congr 1
      omega
    have := Nat.min_le_right f s
    omega

theorem minimum_family_lower (c m L bound : ℕ)
    (feasible : c+L+1≤m) (h : bound≤L) :
    c+1+bound≤m := by omega

/-- Summed availability and confidentiality budgets imply the exact
endpoint feasibility cutoff, even with duplicate capsules. -/
theorem averaged_cut (n c r f M B L : ℕ) (hn : 0<n) (hr : 0<r)
    (corruptionUpper : c*M≤n*B) (availabilityUpper : f*M≤n*L)
    (required : B+r*L+r≤M) : c+r*f<n := by
  by_contra h
  have cross := Nat.mul_le_mul_right M (Nat.le_of_not_gt h)
  have loss := Nat.mul_le_mul_left r availabilityUpper
  have sum := Nat.mul_le_mul_left n required
  have np : 0<n*r := Nat.mul_pos hn hr
  nlinarith

theorem saturated_budget (n c r f : ℕ) (hn : 0<n) (enough : c+r*f+1≤n) :
    c+1+minLoss n f (r*n)≤n := by
  have nz : n≠0 := by omega
  unfold minLoss
  rw [Nat.mul_div_cancel r hn, Nat.mul_mod_left]
  simp only [Nat.min_zero, add_zero]
  simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using enough

/-- Each cyclic family interval of length at most n uses distinct domains. -/
theorem cyclic_no_duplicate (n start i j : ℕ) (hi : i<n) (hj : j<n)
    (h : (start+i)%n=(start+j)%n) : i=j := by
  have h' : start+i ≡ start+j [MOD n] := h
  have e : i%n=j%n := Nat.ModEq.add_left_cancel' start h'
  rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at e

example : minLoss 9 2 (3*9)=6 ∧ 3*9=27 ∧ 3*(2+2+1)=15 := by decide

#print axioms cyclic_no_duplicate
#print axioms top_lower
#print axioms minimum_family_lower
#print axioms averaged_cut
#print axioms saturated_budget

end ManyFamilies
