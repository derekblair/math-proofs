import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators
namespace WeightedMoment

theorem cartesian_count {L R J : Type} (outer : Finset J) (left : J → Finset L)
    (right : J → Finset R) :
    (∑ j ∈ outer, ∑ _a ∈ left j, ∑ _b ∈ right j, (1 : ℕ)) =
      ∑ j ∈ outer, (left j).card * (right j).card := by
  simp

theorem weighted_light {J : Type} (outer : Finset J)
    (leftDegree rightDegree : J → ℕ) (cap : ℕ)
    (h : ∀ j ∈ outer, rightDegree j ≤ cap) :
    (∑ j ∈ outer, leftDegree j * rightDegree j) ≤
      cap * ∑ j ∈ outer, leftDegree j := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [Nat.mul_comm cap]
  exact Nat.mul_le_mul_left _ (h j hj)

#print axioms cartesian_count
#print axioms weighted_light
end WeightedMoment
