import RefreshCollisionTop

namespace RefreshCollisionEntropy
open scoped BigOperators

/-- Natural-log Shannon entropy is at least minus the logarithm of
    collision probability. A zero probability contributes zero. -/
theorem shannon_at_least_collision {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (ht : (∑ i, p i)=1)
    (A : ℝ) (hA : (∑ i, (p i)^2) ≤ A) :
    -Real.log A ≤ -(∑ i, p i * Real.log (p i)) := by
  classical
  let C : ℝ := ∑ i, (p i)^2
  have hnonzero : ∃ i, p i ≠ 0 := by
    by_contra he
    push_neg at he
    simp [he] at ht
  obtain ⟨i, hi⟩ := hnonzero
  have hCpos : 0 < C :=
    (sq_pos_of_ne_zero hi).trans_le (Finset.single_le_sum
      (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i))
  have hpoint (j : ι) :
      p j * Real.log (p j) - p j * Real.log C ≤ (p j)^2/C-p j := by
    by_cases hz : p j=0
    · simp [hz]
    · have hj := lt_of_le_of_ne (hp j) (Ne.symm hz)
      have he := Real.log_le_sub_one_of_pos (div_pos hj hCpos)
      rw [Real.log_div hz hCpos.ne'] at he
      have hm := mul_le_mul_of_nonneg_left he (hp j)
      calc
        _ = p j * (Real.log (p j) - Real.log C) := by ring
        _ ≤ p j * (p j/C-1) := hm
        _ = _ := by ring
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpoint j)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.sum_div, ht, one_mul] at hsum
  change (∑ i, p i * Real.log (p i))-Real.log C ≤ C/C-1 at hsum
  rw [div_self hCpos.ne', sub_self] at hsum
  have hlog : Real.log C ≤ Real.log A := Real.log_le_log hCpos hA
  linarith

end RefreshCollisionEntropy
#print axioms RefreshCollisionEntropy.shannon_at_least_collision
