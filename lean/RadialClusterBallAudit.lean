import Mathlib.Tactic

/-! Algebra only; the asymptotic and probabilistic claims are not formalized. -/

namespace RadialClusterBallAudit

theorem quadratic_max (a b c t m : ℝ) (hc : c ≤ 0) (hs : b + 2*c*m = 0) :
    a + b*t + c*t^2 ≤ a + b*m + c*m^2 := by
  have hneg := mul_nonpos_of_nonpos_of_nonneg hc (sq_nonneg (t-m))
  have hz := congrArg (fun x : ℝ => x * (t-m)) hs
  nlinarith [hneg, hz]

theorem radial_boundary_quadratic (A r z t : ℝ) :
    (A + 2*r*t)^2 + z^2 - 2*(A + 2*r*t)*z*t =
    (A^2 + z^2) + (4*A*r - 2*A*z)*t + (4*r^2 - 4*r*z)*t^2 := by
  ring

theorem midpoint_ball_sq (g x a b : ℝ)
    (ha : (x-a)^2 ≤ g^2) (hb : (x-b)^2 ≤ g^2) :
    (x-(a+b)/2)^2 + (a-b)^2/4 ≤ g^2 := by
  have h : (x-(a+b)/2)^2 + (a-b)^2/4 = ((x-a)^2 + (x-b)^2)/2 := by ring
  rw [h]; linarith

#print axioms quadratic_max
#print axioms radial_boundary_quadratic
#print axioms midpoint_ball_sq
end RadialClusterBallAudit
