import PetersenArithmetic
open scoped BigOperators
namespace SparseHalfStability

/-- Scalar end of the Norin–Yepremyan disturbed-subgraph argument,
with actual cardinalities (and hence no division by the graph order). -/
theorem edit_scalar (c eps n m added missing : ℝ)
    (hc : 0 ≤ c) (hn : 0 ≤ n) (hm : 0 ≤ m) (hM : m ≤ eps*n)
    (hE : 2*(1+c)*eps ≤ c^2)
    (hA : added ≤ 2*eps*n*m)
    (hB : m*(c*n-2*m) ≤ missing) :
    added ≤ c*missing := by
  have h1 := mul_nonneg hc (sub_nonneg.mpr hM)
  have h2 := mul_nonneg hn (sub_nonneg.mpr hE)
  have h3 : 2*eps*n ≤ c*(c*n-2*m) := by nlinarith
  have h4 := mul_le_mul_of_nonneg_left h3 hm
  have h5 := mul_le_mul_of_nonneg_left hB hc
  nlinarith

/-- Given the edge cardinality transfer and the baseline edgewise uniform
bounds, the expected total cost does not increase. -/
theorem cost_transfer {E : Type*} [DecidableEq E]
    (base actual : Finset E) (f : E → ℝ) (c maxWeight : ℝ)
    (hc : 0 ≤ maxWeight)
    (counts : ((actual \ base).card : ℝ) ≤ c*(base \ actual).card)
    (plus : ∀ e ∈ actual \ base, f e ≤ maxWeight)
    (minus : ∀ e ∈ base \ actual, c*maxWeight ≤ f e) :
    (∑ e ∈ actual, f e) ≤ ∑ e ∈ base, f e := by
  have ha := Finset.sum_le_sum plus
  have hb := Finset.sum_le_sum minus
  simp only [Finset.sum_const, nsmul_eq_mul] at ha hb
  have ht := mul_le_mul_of_nonneg_right counts hc
  have heA := Finset.sum_sdiff (f := f) (Finset.inter_subset_left : actual ∩ base ⊆ actual)
  have heB := Finset.sum_sdiff (f := f) (Finset.inter_subset_right : actual ∩ base ⊆ base)
  have hv : actual \ (actual ∩ base) = actual \ base := by
    ext e
    by_cases h : e ∈ actual <;> simp [h]
  rw [hv] at heA
  have hu : base \ (actual ∩ base) = base \ actual := by
    ext e
    by_cases h : e ∈ base <;> simp [h]
  rw [hu] at heB
  nlinarith

#print axioms edit_scalar
#print axioms cost_transfer
end SparseHalfStability
