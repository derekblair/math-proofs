import GeometricChartConditional

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped ENNReal

theorem projectionMass_nonzero_finite (k m : ℕ) :
    projectionMass k m≠0 ∧ projectionMass k m≠∞ := by
  let W := EuclideanSpace ℝ (Fin (m+2))
  let U := SphereAmbient (Fin k) W
  letI : Nontrivial W := Module.nontrivial_of_finrank_pos (by
    change 0<Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+2)))
    simp)
  letI : Nontrivial U :=
    (WithLp.linearEquiv 2 ℝ (EuclideanSpace ℝ (Fin k)×W)).symm.injective.nontrivial
  let ν := (volume : Measure W)
  let μ := (volume : Measure U)
  let h := reciprocalRadial (Fintype.card (Fin k)+m+1)
  have dm : Module.finrank ℝ W=m+2 := by simp [W]
  have ra : (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^(Fintype.card (Fin k)+m+1))*h r) = 1 :=
    reciprocalRadial_integral _
  have law := spherical_projection_unnormalized (W:=W) m dm
    (fun _ : Fin k→ℝ => (1:ℝ≥0∞)) measurable_const h (reciprocalRadial_measurable _)
    (by rw [ra]; exact one_ne_zero) (by rw [ra]; exact ENNReal.one_ne_top)
  simp only [lintegral_const,one_mul,mul_one] at law
  change μ.toSphere univ = ν.toSphere univ * projectionMass k m at law
  have eu : μ.toSphere univ≠0 := by
    intro n
    exact μ.toSphere_ne_zero (Measure.measure_univ_eq_zero.mp n)
  have et : μ.toSphere univ≠∞ := measure_ne_top _ _
  have vu : ν.toSphere univ≠0 := by
    intro n
    exact ν.toSphere_ne_zero (Measure.measure_univ_eq_zero.mp n)
  constructor
  · intro z
    rw [z,mul_zero] at law
    exact eu law
  · intro z
    rw [z,ENNReal.mul_top vu] at law
    exact et law

#print axioms projectionMass_nonzero_finite
end RobustFolkman.GeometricGap
