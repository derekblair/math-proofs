import GeometricPairGraphMeasure
import GeometricCapProbability

namespace RobustFolkman.GeometricGap
open MeasureTheory Set Finset WithLp
open scoped InnerProductSpace ENNReal
variable {J E F : Type*} [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] [Nontrivial F]

theorem root_predicate_graph_isometry (f : E≃ₗᵢ[ℝ] F) (t : ℝ) (a : UnitSphere E)
    (x : J→UnitSphere E) :
    samplePredicateGraph (triangleAt t (sphereTransport f a)) (fun i => sphereTransport f (x i)) =
      samplePredicateGraph (triangleAt t a) x := by
  ext e
  rw [samplePredicate_edge_eq,samplePredicate_edge_eq]
  have h (i j : J) : (sphereTransport f (x i),sphereTransport f (x j))∈
      triangleAt t (sphereTransport f a) ↔ (x i,x j)∈triangleAt t a := by
    simp only [triangleAt,mem_ofPred_eq,sphereTransport_val,f.inner_map_map]
  simp_rw [h]

theorem sampleBadCut_measurable (t : ℝ) (a : UnitSphere E) :
    MeasurableSet {x : J→UnitSphere E | sampleBadCut t a x} := by
  change MeasurableSet {x : J→UnitSphere E |
    (fun G : EdgeGraph J => ∃ b : J→Bool, (5/8:ℝ)*(G.card:ℝ)<cutCount G b)
      (samplePredicateGraph (triangleAt t a) x)}
  exact measurable_sample_predicate (J:=J) _ (triangleAt_measurable t a) (fun G => ∃ b : J→Bool, (5/8:ℝ)*(G.card:ℝ)<cutCount G b)

theorem root_sample_bad_probability_isometry (f : E≃ₗᵢ[ℝ] F) (t : ℝ) (a : UnitSphere E) :
    (Measure.pi (fun _ : J => uniformSphere (volume : Measure E))).real {x | sampleBadCut t a x} =
      (Measure.pi (fun _ : J => uniformSphere (volume : Measure F))).real
        {x | sampleBadCut t (sphereTransport f a) x} := by
  let σ := uniformSphere (volume : Measure E)
  let τ := uniformSphere (volume : Measure F)
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  letI : IsProbabilityMeasure τ := uniformSphere_isProbability _
  have p := measurePreserving_pi (fun _ : J => σ) (fun _ => τ) (fun _ => sphereTransport_volume f)
  let B := {x : J→UnitSphere F | sampleBadCut t (sphereTransport f a) x}
  have h := p.measure_preimage (sampleBadCut_measurable (J:=J) t (sphereTransport f a)).nullMeasurableSet
  change (Measure.pi (fun _ : J => σ)) ((fun x : J→UnitSphere E => fun i => sphereTransport f (x i)) ⁻¹' B)
    = (Measure.pi (fun _ : J => τ)) B at h
  have eq : (fun x : J→UnitSphere E => fun i => sphereTransport f (x i)) ⁻¹' B =
      {x : J→UnitSphere E | sampleBadCut t a x} := by
    ext x
    simp only [B,Set.mem_preimage,mem_ofPred_eq,sampleBadCut,root_predicate_graph_isometry]
  rw [eq] at h
  exact congrArg ENNReal.toReal h

theorem root_cap_probability_isometry (f : E≃ₗᵢ[ℝ] F) (t : ℝ) (a : UnitSphere E) :
    (uniformSphere (volume : Measure E)).real (capPoints t a)=
      (uniformSphere (volume : Measure F)).real (capPoints t (sphereTransport f a)) := by
  have h := (sphereTransport_volume f).measure_preimage
    (capPoints_measurable t (sphereTransport f a)).nullMeasurableSet
  have eq : (sphereTransport f) ⁻¹' capPoints t (sphereTransport f a)=capPoints t a := by
    ext x
    change t≤⟪(sphereTransport f a).val,(sphereTransport f x).val⟫_ℝ ↔ t≤⟪a.val,x.val⟫_ℝ
    simp only [sphereTransport_val,f.inner_map_map]
  rw [eq] at h
  exact congrArg ENNReal.toReal h

#print axioms root_sample_bad_probability_isometry
#print axioms root_cap_probability_isometry
end RobustFolkman.GeometricGap
