import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

namespace Erdős151
open scoped BigOperators

variable {L R : Type*}

def colCount (S : Finset L) (rel : L → R → Prop) [DecidableRel rel] (x : R) : ℕ :=
  (S.filter (fun u => rel u x)).card

def rowCount (X : Finset R) (rel : L → R → Prop) [DecidableRel rel] (u : L) : ℕ :=
  (X.filter (rel u)).card

theorem flipCounts (S : Finset L) (X : Finset R) (rel : L → R → Prop) [DecidableRel rel] :
    ∑ x ∈ X, colCount S rel x = ∑ u ∈ S, rowCount X rel u := by
  unfold colCount rowCount
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

/-- Double-count a weighted pair of incidence relations with a per-source
capacity and per-sink mandatory demand. The two relations can overlap. -/
theorem incidence_budget (S : Finset L) (X : Finset R)
    (priv lp : L → R → Prop) [DecidableRel priv] [DecidableRel lp]
    (A B cap : ℕ) (demand : R → ℕ)
    (hlo : ∀ x ∈ X, demand x ≤ A * colCount S priv x + B * colCount S lp x)
    (hhi : ∀ u ∈ S, A * rowCount X priv u + B * rowCount X lp u ≤ cap) :
    ∑ x ∈ X, demand x ≤ S.card * cap := by
  calc
    ∑ x ∈ X, demand x ≤ ∑ x ∈ X, (A * colCount S priv x + B * colCount S lp x) :=
      Finset.sum_le_sum hlo
    _ = ∑ u ∈ S, (A * rowCount X priv u + B * rowCount X lp u) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, flipCounts]
    _ ≤ ∑ _u ∈ S, cap := Finset.sum_le_sum hhi
    _ = S.card * cap := by rw [Finset.sum_const]; exact nsmul_eq_mul S.card cap

/-- Weighted private capacity at an owner in the ambient-degree-9 stage. -/
theorem private_nine_capacity (s ell : ℕ)
    (hs : s ≤ 5) (he : ell ≤ 2) (h1 : ell = 1 → s ≤ 3)
    (h2 : ell = 2 → s ≤ 2) : 2*s+3*ell ≤ 10 := by
  by_cases h : ell=0
  · omega
  by_cases k : ell=1
  · have hh := h1 k
    omega
  have hk : ell=2 := by omega
  have hhh := h2 hk
  omega

#print axioms flipCounts
#print axioms incidence_budget
#print axioms private_nine_capacity
end Erdős151
