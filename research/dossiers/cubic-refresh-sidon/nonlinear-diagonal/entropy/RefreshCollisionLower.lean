import RefreshCollisionShannon

namespace RefreshCollisionEntropy
open scoped BigOperators

/-- For a probability law split at the k-th heaviest atom and with
    the indicated top-k probability cap, H ≥ log(k/c) in nats. -/
theorem top_cap_entropy_lower (k l : ℕ) (f : Fin k → ℝ) (g : Fin l → ℝ)
    (c y : ℝ) (hk : 0 < k) (hc : 0 < c) (hy : 0 ≤ y)
    (hf : ∀ i, y ≤ f i) (hg : ∀ j, 0 ≤ g j ∧ g j ≤ y)
    (hkc : (k : ℝ) * c ≤ 1)
    (hcap : (∑ i, f i) ≤ c)
    (hnorm : (∑ i, f i) + (∑ j, g j) = 1) :
    Real.log ((k : ℝ)/c) ≤
      -((∑ i, f i * Real.log (f i)) + (∑ j, g j * Real.log (g j))) := by
  let p := Sum.elim f g
  have hp (i : Fin k ⊕ Fin l) : 0 ≤ p i := by
    cases i with
    | inl i => exact hy.trans (hf i)
    | inr j => exact (hg j).1
  have hs : (∑ i, p i)=1 := by simpa [p, Fintype.sum_sum_type] using hnorm
  have ht : (∑ i, (p i)^2) ≤ c/k := by
    simpa [p, Fintype.sum_sum_type] using top_collision_bound k l f g c y hk hy hf hg hkc hcap hnorm
  have h := shannon_at_least_collision p hp hs _ ht
  have hre : -Real.log (c/(k : ℝ)) = Real.log ((k : ℝ)/c) := by
    have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
    rw [Real.log_div hc.ne' hkr.ne', Real.log_div hkr.ne' hc.ne']
    ring
  rw [hre] at h
  simpa [p, Fintype.sum_sum_type] using h

end RefreshCollisionEntropy
#print axioms RefreshCollisionEntropy.top_cap_entropy_lower
