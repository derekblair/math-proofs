import GeometricSphereTransitive

namespace RobustFolkman
open MeasureTheory Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

def triangleAt (t : ℝ) (a : UnitSphere E) : Set (UnitSphere E × UnitSphere E) :=
  {bc | t≤⟪(a:E),(bc.1:E)⟫_ℝ ∧ t≤⟪(a:E),(bc.2:E)⟫_ℝ ∧ t≤⟪(bc.1:E),(bc.2:E)⟫_ℝ}

theorem triangleAt_measurable (t : ℝ) (a : UnitSphere E) :
    MeasurableSet (triangleAt t a) := by
  have b : Continuous (fun bc : UnitSphere E×UnitSphere E => (bc.1:E)) :=
    continuous_subtype_val.comp continuous_fst
  have c : Continuous (fun bc : UnitSphere E×UnitSphere E => (bc.2:E)) :=
    continuous_subtype_val.comp continuous_snd
  exact (measurableSet_le measurable_const (continuous_const.inner (𝕜:=ℝ) b).measurable).inter
    ((measurableSet_le measurable_const (continuous_const.inner (𝕜:=ℝ) c).measurable).inter
      (measurableSet_le measurable_const (b.inner (𝕜:=ℝ) c).measurable))

theorem triangleAt_measure_root_independent [Nontrivial E] (t : ℝ) (a b : UnitSphere E) :
    let σ := uniformSphere (volume : Measure E)
    (σ.prod σ) (triangleAt t a) = (σ.prod σ) (triangleAt t b) := by
  intro σ
  let _ : IsProbabilityMeasure σ := uniformSphere_isProbability volume
  obtain ⟨e,h,pres⟩ := uniformSphere_transitive a b
  let f := sphereRotation e
  have hp : MeasurePreserving (Prod.map f f) (σ.prod σ) (σ.prod σ) := pres.prod pres
  have pre : (Prod.map f f) ⁻¹' triangleAt t b = triangleAt t a := by
    ext uv
    rcases uv with ⟨u,v⟩
    have bval : (b:E)=e a := by
      rw [←h,sphereRotation_val]
    change (t≤⟪(b:E),(f u:E)⟫_ℝ ∧ t≤⟪(b:E),(f v:E)⟫_ℝ ∧
      t≤⟪(f u:E),(f v:E)⟫_ℝ) ↔
      (t≤⟪(a:E),(u:E)⟫_ℝ ∧ t≤⟪(a:E),(v:E)⟫_ℝ ∧ t≤⟪(u:E),(v:E)⟫_ℝ)
    simp only [f,bval,sphereRotation_val,e.inner_map_map]
  have H := hp.measure_preimage (triangleAt_measurable t b).nullMeasurableSet
  rwa [pre] at H

#print axioms triangleAt_measure_root_independent
end RobustFolkman
