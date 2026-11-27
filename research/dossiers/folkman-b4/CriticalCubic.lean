import CriticalCard
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace FolkmanB4.Critical
open Finset
variable {L V : Type*} [Fintype L] [Fintype V] (I : L → V → Prop)
variable [DecidableRel I]

def pts (l : L) : Nat := (univ.filter (fun v => I l v)).card
def lns (v : V) : Nat := (univ.filter (fun l => I l v)).card

theorem counts :
    ∑ l, pts I l = ∑ v, lns I v := by
  have p (l : L) : pts I l=∑ v : V, if I l v then 1 else 0 := by
    rw [←sum_filter]
    simp [pts]
  have q (v : V) : lns I v=∑ l : L, if I l v then 1 else 0 := by
    rw [←sum_filter]
    simp [lns]
  simp only [p,q]
  exact sum_comm

/-- The critical core is square and every point lies on three lines. -/
theorem cubic (used : ∀ v, ∃ l, I l v)
    (bad : ¬∃ c, Good I univ c)
    (minimal : ∀ S : Finset L, S ≠ univ → ∃ c, Good I S c)
    (row : ∀ l, pts I l=3) (col : ∀ v, lns I v≤3) :
    Fintype.card V = Fintype.card L ∧ ∀ v, lns I v=3 := by
  classical
  have cc := counts I
  simp only [row,sum_const,card_univ,nsmul_eq_mul] at cc
  change Fintype.card L * 3 = ∑ v, lns I v at cc
  have bd : (∑ v : V, lns I v) ≤ Fintype.card V*3 := by
    calc
      _ ≤ ∑ v : V, 3 := sum_le_sum fun v _ => col v
      _ = _ := by simp
  have n := card_le_lines I used bad minimal
  have e : Fintype.card V=Fintype.card L := by omega
  refine ⟨e,fun v => ?_⟩
  by_contra neq
  have tight : lns I v<3 := lt_of_le_of_ne (col v) neq
  have small : (∑ v : V, lns I v) < ∑ v : V, 3 :=
    sum_lt_sum (fun w _ => col w) ⟨v,mem_univ v,tight⟩
  simp at small
  omega

#print axioms cubic
end FolkmanB4.Critical
