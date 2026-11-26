import Mathlib.Tactic

open scoped BigOperators
namespace Interval3SUM

/-- The left and right edge incidences of the middle graph can be charged
to the interval lengths, rather than to a separate full graph per batch. -/
theorem mass {I : Type*} (levels : Finset ℕ) (intervals : ℕ → Finset I)
    (len : I → ℕ) (edge : ℕ → I → ℕ) (width rate : ℕ)
    (disjoint_mass : ∀ j ∈ levels, ∑ i ∈ intervals j, len i ≤ width)
    (local_mass : ∀ j ∈ levels, ∀ i ∈ intervals j, edge j i ≤ rate * len i) :
    (∑ j ∈ levels, ∑ i ∈ intervals j, edge j i) ≤ levels.card * (rate * width) := by
  calc
    _ ≤ ∑ _j ∈ levels, rate * width := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        _ ≤ ∑ i ∈ intervals j, rate * len i :=
          Finset.sum_le_sum (local_mass j hj)
        _ = rate * (∑ i ∈ intervals j, len i) := by rw [Finset.mul_sum]
        _ ≤ _ := Nat.mul_le_mul_left _ (disjoint_mass j hj)
    _ = _ := by simp

/-- A single graph's heavy vertices and light wedges share the budget
of its genuine incident edges, independently of queried endpoint pairs. -/
theorem split {V : Type*} [DecidableEq V] (m : Finset V)
    (left right : V → ℕ) (delta : ℕ) :
    let total := ∑ v ∈ m, (left v + right v)
    (m.filter (fun v : V => delta < left v + right v)).card * (delta + 1) ≤ total ∧
      (∑ v ∈ m.filter (fun v : V => left v + right v ≤ delta), left v * right v) ≤
        delta * total := by
  dsimp only
  constructor
  · let h := m.filter (fun v : V => delta < left v + right v)
    calc
      h.card * (delta + 1) = ∑ _v ∈ h, (delta+1) := by simp
      _ ≤ ∑ v ∈ h, (left v + right v) := by
        apply Finset.sum_le_sum
        intro v hv
        exact Nat.succ_le_of_lt (Finset.mem_filter.mp hv).2
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  · let l := m.filter (fun v : V => left v + right v ≤ delta)
    calc
      _ ≤ ∑ v ∈ l, delta * (left v + right v) := by
        apply Finset.sum_le_sum
        intro v hv
        have hd : left v + right v ≤ delta := (Finset.mem_filter.mp hv).2
        exact Nat.mul_le_mul (by omega) (by omega)
      _ = delta * (∑ v ∈ l, (left v + right v)) := by rw [Finset.mul_sum]
      _ ≤ _ := Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))

end Interval3SUM
#print axioms Interval3SUM.mass
#print axioms Interval3SUM.split
