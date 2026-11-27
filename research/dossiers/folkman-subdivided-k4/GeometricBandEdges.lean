import GeometricBandResidualLaw
import GeometricThinShellBracket

namespace RobustFolkman.GeometricGap
open MeasureTheory Set WithLp
open scoped ENNReal InnerProductSpace
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]

noncomputable def sphereHeight (u : UnitSphere (SphereAmbient (Fin 1) W)) : ℝ :=
  sphereCoord u 0

theorem sphere_residual_radius (u : UnitSphere (SphereAmbient (Fin 1) W)) :
    ‖(ofLp u.val).2‖^2=1-(sphereHeight u)^2 := by
  have h : ‖u.val‖=1 := by simpa [Metric.mem_sphere,dist_zero_right] using u.property
  have n := WithLp.prod_norm_sq_eq_of_L2 u.val
  rw [show ‖u.val‖^2=1 from by simp [h]] at n
  change 1=‖(ofLp u.val).1‖^2+‖(ofLp u.val).2‖^2 at n
  rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_one] at n
  change 1=(sphereHeight u)^2+‖(ofLp u.val).2‖^2 at n
  linarith only [n]

theorem residualDirection_rescale (w : W) (h : w≠0) :
    ‖w‖ • (residualDirection w).val=w := by
  have hn := (norm_pos_iff.mpr h).ne'
  simp [residualDirection,h,smul_smul,hn]

theorem inner_height_direction (u v : UnitSphere (SphereAmbient (Fin 1) W))
    (u0 : (ofLp u.val).2≠0) (v0 : (ofLp v.val).2≠0) :
    ⟪u.val,v.val⟫_ℝ = sphereHeight u*sphereHeight v +
      (‖(ofLp u.val).2‖*‖(ofLp v.val).2‖)*⟪(sphereResidual u).val,(sphereResidual v).val⟫_ℝ := by
  rw [WithLp.prod_inner_apply]
  change ⟪(ofLp u.val).1,(ofLp v.val).1⟫_ℝ + ⟪(ofLp u.val).2,(ofLp v.val).2⟫_ℝ = _
  rw [PiLp.inner_apply,Fin.sum_univ_one]
  have lhs : ⟪(ofLp (ofLp u.val).1) 0,(ofLp (ofLp v.val).1) 0⟫_ℝ =
      sphereHeight u*sphereHeight v := by
    change ⟪sphereHeight u,sphereHeight v⟫_ℝ = _
    rw [real_inner_comm, RCLike.inner_apply]
    simp
  rw [lhs]
  nth_rw 1 [←residualDirection_rescale (ofLp u.val).2 u0, ←residualDirection_rescale (ofLp v.val).2 v0]
  rw [real_inner_smul_left,real_inner_smul_right]
  simp only [sphereResidual]
  ring

theorem residual_radius_product (u v : UnitSphere (SphereAmbient (Fin 1) W)) :
    ‖(ofLp u.val).2‖*‖(ofLp v.val).2‖ =
      Real.sqrt ((1-(sphereHeight u)^2)*(1-(sphereHeight v)^2)) := by
  rw [←sphere_residual_radius u,←sphere_residual_radius v,Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _),Real.sqrt_sq (norm_nonneg _)]

theorem shell_edge_residual_iff (u v : UnitSphere (SphereAmbient (Fin 1) W))
    (t : ℝ) (u0 : (ofLp u.val).2≠0) (v0 : (ofLp v.val).2≠0) :
    t≤⟪u.val,v.val⟫_ℝ ↔
      residualThreshold t (sphereHeight u) (sphereHeight v)≤
        ⟪(sphereResidual u).val,(sphereResidual v).val⟫_ℝ := by
  have p : 0<‖(ofLp u.val).2‖*‖(ofLp v.val).2‖ :=
    mul_pos (norm_pos_iff.mpr u0) (norm_pos_iff.mpr v0)
  rw [inner_height_direction u v u0 v0,residualThreshold,←residual_radius_product]
  rw [div_le_iff₀ p]
  constructor <;> intro h <;> linarith only [h,
    mul_comm (‖(ofLp u.val).2‖*‖(ofLp v.val).2‖)
      ⟪(sphereResidual u).val,(sphereResidual v).val⟫_ℝ]

theorem actual_shell_link_bracket (u v : UnitSphere (SphereAmbient (Fin 1) W))
    (t w : ℝ) (t0 : 0<t) (t1 : t≤1/8) (w0 : 0≤w) (w1 : w≤t)
    (uL : t≤sphereHeight u) (uR : sphereHeight u≤t+w)
    (vL : t≤sphereHeight v) (vR : sphereHeight v≤t+w) :
    (t/(1+t)≤⟪(sphereResidual u).val,(sphereResidual v).val⟫_ℝ → t≤⟪u.val,v.val⟫_ℝ) ∧
    (t≤⟪u.val,v.val⟫_ℝ →
      t/(1+t)-4*t*w≤⟪(sphereResidual u).val,(sphereResidual v).val⟫_ℝ) := by
  have hp (z : UnitSphere (SphereAmbient (Fin 1) W)) (hL : t≤sphereHeight z)
      (hR : sphereHeight z≤t+w) : (ofLp z.val).2≠0 := by
    intro zz
    have ha := sphere_residual_radius z
    rw [zz,norm_zero,zero_pow (by decide)] at ha
    have m : sphereHeight z≤1/4 := by linarith only [hR,t1,w1]
    have s := pow_le_pow_left₀ (t0.le.trans hL) m 2
    linarith only [ha,s]
  have uu := hp u uL uR
  have vv := hp v vL vR
  have br := residual_threshold_thin_shell t w (sphereHeight u) (sphereHeight v)
    t0 t1 w0 w1 uL uR vL vR
  rw [shell_edge_residual_iff u v t uu vv]
  exact ⟨fun h => br.2.trans h,fun h => br.1.trans h⟩

#print axioms actual_shell_link_bracket
end RobustFolkman.GeometricGap
