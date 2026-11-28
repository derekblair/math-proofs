import UnblockingIncidence

namespace Erdős151
open scoped BigOperators
variable {V : Type*}

/-- One shared, pointwise form of the two small-support charging arguments.
s and l count neighbors and lone neighbors; p and q count private and
private-lone owners. -/
theorem blocked_lower_charge (s l p q : ℕ)
    (hl : l ≤ s)
    (positive : 1 ≤ s)
    (h1 : s = 1 → l = 1 ∧ 1 ≤ p ∧ 1 ≤ q)
    (h20 : s = 2 → l = 0 → 2 ≤ p)
    (h21 : s = 2 → l = 1 → 1 ≤ p ∧ 1 ≤ q) :
    12 ≤ 4*s+3*(p+q)+2*l ∧ 12 ≤ 4*s+2*p+3*q+3*l := by
  by_cases hs1 : s = 1
  · obtain ⟨_,_,_⟩ := h1 hs1
    omega
  by_cases hs2 : s = 2
  · by_cases hl0 : l = 0
    · have hh := h20 hs2 hl0
      omega
    by_cases hl1 : l = 1
    · have hh := h21 hs2 hl1
      omega
    omega
  omega

theorem blocked_lower_charge_no_lone (s p : ℕ) (positive : 2 ≤ s)
    (h2 : s = 2 → 2 ≤ p) : 6 ≤ 2*s+p := by
  by_cases h : s = 2
  · have hp := h2 h
    omega
  · omega

/-- Sum a local three-resource inequality without introducing case-set counts. -/
theorem sum_charges (X : Finset V) (s p l : V → ℕ) (K A B C : ℕ)
    (h : ∀ x ∈ X, K ≤ A*s x+B*p x+C*l x) :
    K*X.card ≤ A*(∑ x ∈ X, s x)+B*(∑ x ∈ X, p x)+C*(∑ x ∈ X, l x) := by
  calc
    K*X.card = ∑ _ ∈ X, K := by rw [Finset.sum_const]; exact (Nat.mul_comm K X.card).trans (nsmul_eq_mul X.card K).symm
    _ ≤ ∑ x ∈ X, (A*s x+B*p x+C*l x) := Finset.sum_le_sum h
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]

#print axioms blocked_lower_charge
#print axioms blocked_lower_charge_no_lone
#print axioms sum_charges
end Erdős151
