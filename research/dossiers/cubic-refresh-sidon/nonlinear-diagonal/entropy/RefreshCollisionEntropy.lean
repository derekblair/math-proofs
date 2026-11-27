import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace RefreshCollisionEntropy
open scoped BigOperators

/-- Once the mass above the k-th atom is concentrated in one atom, this
    scalar inequality bounds the collision probability of the sampler. -/
theorem concentration_bound (k c y X : ℝ) (hk : 1 ≤ k) (hy : 0 ≤ y)
    (hX : y ≤ X) (hkc : k * c ≤ 1) (h : X + (k - 1) * y ≤ c) :
    X^2 + (1-X)*y ≤ c/k := by
  have hk0 : 0 < k := by linarith
  have hk1 : 0 ≤ k-1 := by linarith
  have hky : k*y ≤ c := by linarith
  have hquot : y ≤ c/k := (le_div_iff₀ hk0).2 (by simpa [mul_comm] using hky)
  let A := c - (k-1)*y
  have hAX : X ≤ A := by dsimp [A]; linarith
  have hF : X^2 + (1-X)*y ≤ A^2 + (1-A)*y := by
    have hfac : 0 ≤ (A-X)*(A+X-y) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hterm : k*(k-1)*y^2 ≤ c*(k-1)*y := by
    have hfac := mul_le_mul_of_nonneg_right hky (mul_nonneg hk1 hy)
    calc
      k*(k-1)*y^2 = (k*y)*((k-1)*y) := by ring
      _ ≤ c*((k-1)*y) := hfac
      _ = c*(k-1)*y := by ring
  have hG : A^2+(1-A)*y ≤ c^2+y*(1-k*c) := by
    calc
      A^2+(1-A)*y = c^2 + y*(1-k*c) + (k*(k-1)*y^2-c*(k-1)*y) := by
        dsimp [A]; ring
      _ ≤ c^2+y*(1-k*c) := by linarith
  calc
    _ ≤ A^2 + (1-A)*y := hF
    _ ≤ c^2+y*(1-k*c) := hG
    _ ≤ c^2+(c/k)*(1-k*c) := by
      exact add_le_add_right (mul_le_mul_of_nonneg_right hquot (sub_nonneg.mpr hkc)) _
    _ = c/k := by field_simp <;> ring

end RefreshCollisionEntropy
#print axioms RefreshCollisionEntropy.concentration_bound
