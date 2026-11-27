import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring

open scoped BigOperators
namespace DiagonalWeights
variable {S F : Type*} [DecidableEq S] [Field F]

def weight (m : Nat) (d x : S) : F :=
  1 - if x=d then (2 : F) * (m : F) else 0

theorem sum_eq (m : Nat) (d : S) (A : Finset S) :
    (∑ a ∈ A, weight (F:=F) m d a) =
      (A.card : F) - if d∈A then (2 : F) * (m : F) else 0 := by
  unfold weight
  rw [Finset.sum_sub_distrib]
  simp

theorem roster_zero (m : Nat) (d : S) (A : Finset S) (h : A.card=2*m) (hd : d∈A) :
    (∑ a ∈ A, weight (F:=F) m d a)=0 := by
  rw [sum_eq, if_pos hd, h]
  simp

theorem read_sum_nonzero (m : Nat) (d : S) (A : Finset S) (h : A.card=m)
    (characteristic : (m : F) ≠ 0) : (∑ a ∈ A, weight (F:=F) m d a) ≠ 0 := by
  rw [sum_eq, h]
  by_cases hd : d∈A
  · rw [if_pos hd,show (m:F)-2*(m:F)=-(m:F) by ring]
    exact neg_ne_zero.mpr characteristic
  · simpa [hd] using characteristic

end DiagonalWeights

#print axioms DiagonalWeights.roster_zero
#print axioms DiagonalWeights.read_sum_nonzero
