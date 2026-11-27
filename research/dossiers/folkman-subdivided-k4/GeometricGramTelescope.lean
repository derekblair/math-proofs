import GeometricAnchorCoordinates
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace RobustFolkman.GeometricGap

/-- The previous Gram density, the new coordinates' inverse Jacobian,
and the conditional residual factor telescope to a single power of
the enlarged Gram determinant. -/
theorem gram_density_telescope (D h p : ℝ) (D0 : 0<D) (h0 : 0≤h) :
    D^(p+1/2) * (Real.sqrt D)⁻¹ * h^p = (D*h)^p := by
  rw [Real.rpow_add D0,Real.sqrt_eq_rpow,Real.mul_rpow D0.le h0]
  have d : D^((1:ℝ)/2) ≠ 0 := (Real.rpow_pos_of_pos D0 _).ne'
  calc
    _ = D^p * (D^((1:ℝ)/2) * (D^((1:ℝ)/2))⁻¹) * h^p := by ring
    _ = _ := by rw [mul_inv_cancel₀ d,mul_one]

#print axioms gram_density_telescope
end RobustFolkman.GeometricGap
