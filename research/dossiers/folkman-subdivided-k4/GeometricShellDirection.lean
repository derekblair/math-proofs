import GeometricResidualIndependence
import GeometricProductConditioning

namespace RobustFolkman.GeometricGap
open MeasureTheory Set WithLp
open scoped ENNReal
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]

noncomputable def residualFallback : UnitSphere W :=
  Classical.choice ((NormedSpace.sphere_nonempty (E:=W) (x:=0) (r:=1)).mpr zero_le_one).coe_sort

noncomputable def residualDirection (w : W) : UnitSphere W := by
  classical
  exact if h : w=0 then residualFallback else
    ⟨‖w‖⁻¹ • w,by
      have n : 0<‖w‖ := norm_pos_iff.mpr h
      simp [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,n.le,n.ne']⟩

theorem residualDirection_measurable : Measurable (residualDirection (W:=W)) := by
  classical
  have h : Measurable (fun w : W => if w=0 then (residualFallback (W:=W)).val else ‖w‖⁻¹ • w) := by
    have hc : Measurable (fun _ : W => (residualFallback (W:=W)).val) := measurable_const
    have hg : Measurable (fun w : W => ‖w‖⁻¹ • w) := measurable_norm.inv.smul measurable_id
    exact Measurable.ite (p:=fun w : W => w=0) (measurableSet_singleton (0:W)) hc hg
  have hv : Measurable (fun w : W => (residualDirection w).val) := by
    convert h using 1
    funext w
    by_cases hw : w=0 <;> simp [residualDirection,hw]
  exact hv.subtype_mk

theorem residualDirection_unit (w : UnitSphere W) : residualDirection w.val = w := by
  have hn : ‖w.val‖=1 := by simpa [Metric.mem_sphere,dist_zero_right] using w.property
  have h0 : w.val≠0 := by intro h; simp [h] at hn
  apply Subtype.ext
  simp [residualDirection,h0,hn]

theorem residualDirection_smul (w : W) (b : ℝ) (bp : 0<b) :
    residualDirection (b • w)=residualDirection w := by
  classical
  by_cases w0 : w=0
  · simp [w0]
  have h : b • w≠0 := smul_ne_zero bp.ne' w0
  have hn : 0<‖w‖ := norm_pos_iff.mpr w0
  apply Subtype.ext
  simp only [residualDirection,dif_neg h,dif_neg w0,norm_smul,Real.norm_eq_abs,abs_of_pos bp,smul_smul]
  congr 1
  field_simp [bp.ne',hn.ne']

noncomputable def sphereCoord (u : UnitSphere (SphereAmbient I W)) : I→ℝ :=
  ofLp (ofLp u.val).1

noncomputable def sphereResidual (u : UnitSphere (SphereAmbient I W)) : UnitSphere W :=
  residualDirection (ofLp u.val).2

theorem sphereCoord_measurable : Measurable (sphereCoord (I:=I) (W:=W)) := by
  have eq : sphereCoord (I:=I) (W:=W) = normalizedCoords ∘ Subtype.val :=
    funext fun u => (normalizedCoords_sphere u).symm
  rw [eq]
  exact normalizedCoords_measurable.comp measurable_subtype_coe

theorem sphereResidual_measurable : Measurable (sphereResidual (I:=I) (W:=W)) :=
  residualDirection_measurable.comp <| measurable_snd.comp <|
    (volume_preserving_ofLp (EuclideanSpace ℝ I) W).measurable.comp measurable_subtype_coe

/-- Membership in any measurable height window is independent of
the uniform residual direction, exactly, not just asymptotically. -/
theorem shell_direction_factor (m : ℕ) (dim : Module.finrank ℝ W=m+2)
    (H : Set (I→ℝ)) (S : Set (UnitSphere W)) (hm : MeasurableSet H) (sm : MeasurableSet S) :
    let σ := uniformSphere (volume : Measure (SphereAmbient I W))
    σ ((sphereCoord ⁻¹' H) ∩ (sphereResidual ⁻¹' S)) =
      (uniformSphere (volume : Measure W)) S * σ (sphereCoord ⁻¹' H) := by
  intro σ
  let g : (I→ℝ)→ℝ≥0∞ := H.indicator (fun _ => 1)
  let A : W→ℝ≥0∞ := fun w => S.indicator (fun _ => 1) (residualDirection w)
  have gm : Measurable g := measurable_const.indicator hm
  have am : Measurable A := (measurable_const.indicator sm).comp residualDirection_measurable
  have ah (w : W) (b : ℝ) (bp : 0<b) : A (b • w)=A w := by
    simp only [A,residualDirection_smul w b bp]
  have f := spherical_residual_angular_independence (I:=I) (W:=W) m dim g gm A am ah
  let T := (sphereCoord (I:=I) (W:=W) ⁻¹' H) ∩ (sphereResidual ⁻¹' S)
  have tm : MeasurableSet T := (sphereCoord_measurable hm).inter (sphereResidual_measurable sm)
  have lhs : ∀ u : UnitSphere (SphereAmbient I W),
      A (ofLp u.val).2 * g (ofLp (ofLp u.val).1) = T.indicator (fun _ => (1:ℝ≥0∞)) u := by
    intro u
    by_cases uh : sphereCoord u∈H <;> by_cases us : sphereResidual u∈S <;>
      change (S.indicator (fun _ => (1:ℝ≥0∞)) (sphereResidual u)) *
        H.indicator (fun _ => 1) (sphereCoord u) = _ <;>
      simp [T,uh,us]
  simp_rw [lhs] at f
  rw [lintegral_indicator_const tm,one_mul] at f
  have ax : ∀ u : UnitSphere W, A u.val=S.indicator (fun _ => (1:ℝ≥0∞)) u :=
    fun u => by simp [A,residualDirection_unit]
  simp_rw [ax] at f
  rw [lintegral_indicator_const sm,one_mul] at f
  change σ T = _ * ∫⁻ u, H.indicator (fun _ => (1:ℝ≥0∞)) (sphereCoord u) ∂σ at f
  rw [lintegral_indicator_const_comp sphereCoord_measurable hm,one_mul] at f
  exact f

#print axioms shell_direction_factor
end RobustFolkman.GeometricGap
