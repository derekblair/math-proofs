import GeometricShellDirection
import GeometricCapSelection

namespace RobustFolkman.GeometricGap
open MeasureTheory Set WithLp Finset
open scoped ENNReal
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]

theorem conditioned_residual_uniform (m : ℕ) (dim : Module.finrank ℝ W=m+2)
    (H : Set (I→ℝ)) (hm : MeasurableSet H)
    (h0 : (uniformSphere (volume : Measure (SphereAmbient I W))) (sphereCoord ⁻¹' H) ≠ 0) :
    MeasurePreserving (sphereResidual (I:=I) (W:=W))
      (condOn (uniformSphere (volume : Measure (SphereAmbient I W))) (sphereCoord ⁻¹' H))
      (uniformSphere (volume : Measure W)) := by
  let τ := uniformSphere (volume : Measure W)
  let σ := uniformSphere (volume : Measure (SphereAmbient I W))
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  refine ⟨sphereResidual_measurable,?_⟩
  ext S sm
  rw [Measure.map_apply sphereResidual_measurable sm,condOn,Measure.smul_apply,smul_eq_mul,
    Measure.restrict_apply (sphereResidual_measurable sm),inter_comm,
    shell_direction_factor m dim H S hm sm]
  rw [mul_comm (τ S) _,← mul_assoc,ENNReal.inv_mul_cancel h0 (measure_ne_top σ _),one_mul]

/-- After conditioning on the labels in the height window, extracting
their directions gives an iid uniform tangent-sphere sample. -/
theorem band_residual_selected_event (m : ℕ) (dim : Module.finrank ℝ W=m+2)
    (H : Set (I→ℝ)) (hm : MeasurableSet H)
    (L : Finset J) (B : Set ({i : J // i∈L} → UnitSphere W)) (Bm : MeasurableSet B) :
    let σ := uniformSphere (volume : Measure (SphereAmbient I W))
    let A := sphereCoord ⁻¹' H
    let τ := uniformSphere (volume : Measure W)
    σ A≠0 → σ Aᶜ≠0 →
    (Measure.pi (fun _ : J => σ)).restrict (Set.univ.pi (labelSlices A L))
      ((fun x i => sphereResidual (x i.val)) ⁻¹' B) =
      ((σ A)^L.card*(σ Aᶜ)^(Fintype.card J-L.card)) *
        (Measure.pi (fun _ : {i : J // i∈L} => τ)) B := by
  intro σ A τ a0 a1
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  letI : IsProbabilityMeasure τ := uniformSphere_isProbability _
  have p := conditioned_residual_uniform (I:=I) (W:=W) m dim H hm a0
  let F : ({i : J // i∈L} → UnitSphere (SphereAmbient I W)) → ({i : J // i∈L} → UnitSphere W) :=
    fun y i => sphereResidual (y i)
  have FP : MeasurePreserving F (Measure.pi (fun _ => condOn σ A))
      (Measure.pi (fun _ => τ)) :=
    measurePreserving_pi _ _ (fun _ => p)
  have eq := keepLabels_selected_event σ A a0 a1 L (F ⁻¹' B) (FP.measurable Bm)
  rw [keepLabels_mass_formula,FP.measure_preimage Bm.nullMeasurableSet] at eq
  exact eq

#print axioms band_residual_selected_event
end RobustFolkman.GeometricGap
