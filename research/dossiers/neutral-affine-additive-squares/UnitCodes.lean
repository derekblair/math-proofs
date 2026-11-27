import FiniteBalance

namespace UnitCodes

def code (w : ℤ) : List ℤ :=
  if w = 0 then [1,-1] else List.replicate w.natAbs (if 0 < w then 1 else -1)

theorem total (w : ℤ) : (code w).sum = w := by
  by_cases h : w = 0
  · simp [code,h]
  · simp only [code,ite_eq_right h,List.sum_replicate,nsmul_eq_mul]
    split
    · rename_i hp
      rw [mul_one, Int.natAbs_of_nonneg (by omega)]
    · rename_i hn
      have he : (w.natAbs : ℤ) = -w := by
        have hn' : 0 ≤ -w := by omega
        simpa only [Int.natAbs_neg] using Int.natAbs_of_nonneg hn'
      omega

theorem nonempty (w : ℤ) : code w ≠ [] := by
  by_cases h : w = 0
  · simp [code,h]
  · simp [code,h]

theorem unit (w : ℤ) {k : ℤ} (hk : k ∈ code w) : k = 1 ∨ k = -1 := by
  by_cases h : w = 0
  · simpa [code,h] using hk
  · simp only [code,ite_eq_right h] at hk
    have he := List.eq_of_mem_replicate hk
    split at he <;> tauto

end UnitCodes

#print axioms UnitCodes.total
#print axioms UnitCodes.nonempty
#print axioms UnitCodes.unit
