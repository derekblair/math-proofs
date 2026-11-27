import Mathlib.Analysis.SpecialFunctions.Pow.Real
namespace SparseHalfLowBalancedMass
/-- Scalar certificate for the small-imbalance regime in Razborov's epsilon question. -/
theorem fill_low (ell T i r : ℝ)
    (hell : 0<ell) (hell₁ : ell<1/10)
    (ht : 2*T<1/5-ell)
    (hi : i=3/5-ell-T)
    (hr : r=1/2-i) (hr₀ : 0≤r) :
    r≤ell ∧ (3/10)*r+r^2/2<1/50 := by
  have hhalf : r<ell/2 := by linarith
  have hcap : r<1/20 := by linarith
  have hprod := mul_nonneg hr₀ (show 0≤1/20-r by linarith)
  exact ⟨by linarith, by nlinarith⟩

/-- Quantitative Case 1 slack forces the greedy growth to vanish at the endpoint. -/
theorem case_one (a b : ℝ) (ha : 39/100≤a) (hab : a≤b) :
    (1/2-a)*(b-a)+b*(1/2-b)/2 ≤ a*(1/2-a)/2-(3/100)*(b-a) := by
  have h := mul_nonneg (sub_nonneg.mpr hab) (show 0≤ a+b/2-39/100*(3/2) by linarith)
  have he := mul_nonneg (sub_nonneg.mpr hab) (show 0≤ (3*a+b)/2-78/100 by linarith)
  nlinarith
#print axioms fill_low
#print axioms case_one
end SparseHalfLowBalancedMass
