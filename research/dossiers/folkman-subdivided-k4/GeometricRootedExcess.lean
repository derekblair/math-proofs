import GeometricActualShellBound
import GeometricRootTransport

namespace RobustFolkman.GeometricGap
open MeasureTheory Set WithLp
open scoped ENNReal InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

def fixedRootExcess (t : ℝ) (a : UnitSphere E) (p : UnitSphere E × UnitSphere E) : ThreeReals :=
  (⟪a.val,p.1.val⟫_ℝ-t,⟪a.val,p.2.val⟫_ℝ-t,⟪p.1.val,p.2.val⟫_ℝ-t)

theorem fixedRootExcess_continuous (t : ℝ) (a : UnitSphere E) :
    Continuous (fixedRootExcess t a) := by
  unfold fixedRootExcess
  fun_prop

theorem fixedRootExcess_const (t : ℝ) (a b : UnitSphere E) (S : Set ThreeReals) (sm : MeasurableSet S) :
    let σ := uniformSphere (volume : Measure E)
    (σ.prod σ) (fixedRootExcess t a ⁻¹' S) = (σ.prod σ) (fixedRootExcess t b ⁻¹' S) := by
  intro σ
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  obtain ⟨e,h,pres⟩ := uniformSphere_transitive a b
  let f := sphereRotation e
  have hp := pres.prod pres
  have eq : (fixedRootExcess t b ∘ Prod.map f f)=fixedRootExcess t a := by
    funext q
    have bval : b.val=e a.val := by rw [←h,sphereRotation_val]
    change (⟪b.val,(f q.1).val⟫_ℝ-t,⟪b.val,(f q.2).val⟫_ℝ-t,⟪(f q.1).val,(f q.2).val⟫_ℝ-t) =
      fixedRootExcess t a q
    simp [f,bval,sphereRotation_val,e.inner_map_map,fixedRootExcess]
  have f := hp.measure_preimage
    ((fixedRootExcess_continuous t b).measurable sm).nullMeasurableSet
  change (σ.prod σ) ((fixedRootExcess t b ∘ Prod.map (sphereRotation e) (sphereRotation e)) ⁻¹' S) = _ at f
  rw [eq] at f
  exact f

/-- Every fixed root has exactly the same excess-event distribution as the
first vertex of an iid triple. This applies to the shell-loss event. -/
theorem fixedRootExcess_mass (t : ℝ) (a : UnitSphere E) (S : Set ThreeReals) (sm : MeasurableSet S) :
    let σ := uniformSphere (volume : Measure E)
    (σ.prod σ) (fixedRootExcess t a ⁻¹' S) = excessTriangleMass (E:=E) t S := by
  intro σ
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  let F := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => UnitSphere E) 0
  let H := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitSphere E)
  let Q : Set (UnitSphere E × (UnitSphere E×UnitSphere E)) :=
    {p | fixedRootExcess t p.1 p.2∈S}
  have QM : MeasurableSet Q := by
    have h : Continuous (fun p : UnitSphere E × (UnitSphere E × UnitSphere E) =>
      fixedRootExcess t p.1 p.2) := by unfold fixedRootExcess; fun_prop
    exact h.measurable sm
  have fp : MeasurePreserving F (Measure.pi fun _ : Fin 3 => σ)
      (σ.prod (Measure.pi fun _ : Fin 2 => σ)) :=
    measurePreserving_piFinSuccAbove _ 0
  have hp : MeasurePreserving H (Measure.pi fun _ : Fin 2 => σ) (σ.prod σ) :=
    measurePreserving_piFinTwo _
  have P := ((MeasurePreserving.id σ).prod hp).comp fp
  have Ppre : ((Prod.map id H ∘ F) ⁻¹' Q) =
      (chartExcess t ∘ sampleChart) ⁻¹' S := by
    ext u
    rfl
  have Eq := P.measure_preimage QM.nullMeasurableSet
  change (Measure.pi fun _ : Fin 3 => σ) ((Prod.map id H ∘ F) ⁻¹' Q) =
    (σ.prod (σ.prod σ)) Q at Eq
  rw [Ppre,Measure.prod_apply QM] at Eq
  change excessTriangleMass (E:=E) t S =
    ∫⁻ x : UnitSphere E, (σ.prod σ) (fixedRootExcess t x ⁻¹' S) ∂σ at Eq
  rw [Eq]
  calc
    _ = ∫⁻ _ : UnitSphere E, (σ.prod σ) (fixedRootExcess t a ⁻¹' S) ∂σ := by simp
    _ = _ := lintegral_congr (fun x => (fixedRootExcess_const t x a S sm).symm)

#print axioms fixedRootExcess_mass
end RobustFolkman.GeometricGap
