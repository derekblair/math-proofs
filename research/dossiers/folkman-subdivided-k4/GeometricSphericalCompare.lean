import GeometricHeightDensity
import GeometricSliceCompare

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped ENNReal
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]

private theorem div_preserves_bound (a b c d : ℝ≥0∞) (h : a≤c*b) :
    a/d≤c*(b/d) := by
  simp only [ENNReal.div_eq_inv_mul]
  calc
    _ ≤ d⁻¹*(c*b) := by gcongr
    _ = _ := by ac_rfl

theorem cap_height_preimage (t : ℝ) :
    sphereHeight (W:=W) ⁻¹' Ici t = sphereHeight ⁻¹' Icc t 1 := by
  ext u
  have y := sphere_residual_radius u
  have u1 : sphereHeight u≤1 := by
    by_contra! c
    have s := mul_pos (show 0<sphereHeight u-1 by linarith)
      (show 0<sphereHeight u+1 by linarith)
    nlinarith only [s,y,sq_nonneg ‖(WithLp.ofLp u.val).2‖]
  change t≤sphereHeight u ↔ t≤sphereHeight u ∧ sphereHeight u≤1
  exact ⟨fun a => ⟨a,u1⟩,And.left⟩

theorem spherical_band_positive_fraction (m : ℕ) (dim : Module.finrank ℝ W=m+2)
    (t w : ℝ) (tp : 0<t) (t1 : t≤1/8) (r3 : 3≤(m:ℝ)/2)
    (d : 1≤4*((m:ℝ)/2)*t^2) (wide : 1/(4*((m:ℝ)/2)*t)≤w) (hi : t+w≤1) :
    let σ := uniformSphere (volume : Measure (SphereAmbient (Fin 1) W))
    σ (sphereHeight ⁻¹' Ici t) ≤ ENNReal.ofReal (2*Real.exp 3)*σ (sphereHeight ⁻¹' Icc t (t+w)) := by
  intro σ
  change _ ≤ _
  rw [cap_height_preimage, spherical_height_interval m dim t 1 (by linarith) le_rfl,
    spherical_height_interval m dim t (t+w) (by linarith) hi]
  exact div_preserves_bound _ _ _ _ (lower_band_constant ((m:ℝ)/2) t w r3 tp t1 d wide)

theorem spherical_threshold_gap_small (m : ℕ) (dim : Module.finrank ℝ W=m+2)
    (t s : ℝ) (tp : 0<t) (t1 : t≤1/8) (r3 : 3≤(m:ℝ)/2)
    (d : 1≤4*((m:ℝ)/2)*t^2) (s0 : 0≤s) (st : s≤t) :
    let σ := uniformSphere (volume : Measure (SphereAmbient (Fin 1) W))
    let a := 4*((m:ℝ)/2)*t*s
    σ (sphereHeight ⁻¹' Icc (t-s) t) ≤
      ENNReal.ofReal (a*Real.exp (3+a))*σ (sphereHeight ⁻¹' Ici t) := by
  intro σ a
  rw [cap_height_preimage,spherical_height_interval m dim (t-s) t
    (by linarith only [st]) (by linarith only [t1]),
    spherical_height_interval m dim t 1 (by linarith only [tp]) le_rfl]
  exact div_preserves_bound _ _ _ _ (gap_band_constant ((m:ℝ)/2) t s r3 tp t1 d s0 st)

#print axioms spherical_band_positive_fraction
#print axioms spherical_threshold_gap_small
end RobustFolkman.GeometricGap
