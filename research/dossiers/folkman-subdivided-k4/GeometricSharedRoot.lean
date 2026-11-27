import GeometricRootTriangle

namespace RobustFolkman
open MeasureTheory Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  [Nontrivial E]

abbrev SpherePair (E : Type*) [NormedAddCommGroup E] := UnitSphere E × UnitSphere E

def triangleFromRoot (t : ℝ) : Set (UnitSphere E × SpherePair E) :=
  {s | s.2∈triangleAt t s.1}

def twoTrianglesFromRoot (t : ℝ) : Set (UnitSphere E × (SpherePair E × SpherePair E)) :=
  {s | s.2.1∈triangleAt t s.1 ∧ s.2.2∈triangleAt t s.1}

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem triangleFromRoot_measurable (t : ℝ) :
    MeasurableSet (triangleFromRoot (E:=E) t) := by
  let Z := UnitSphere E × SpherePair E
  have a : Continuous (fun s : Z => (s.1:E)) := continuous_subtype_val.comp continuous_fst
  have b : Continuous (fun s : Z => (s.2.1:E)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have c : Continuous (fun s : Z => (s.2.2:E)) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  exact (measurableSet_le measurable_const (a.inner (𝕜:=ℝ) b).measurable).inter
    ((measurableSet_le measurable_const (a.inner (𝕜:=ℝ) c).measurable).inter
      (measurableSet_le measurable_const (b.inner (𝕜:=ℝ) c).measurable))

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem twoTrianglesFromRoot_measurable (t : ℝ) :
    MeasurableSet (twoTrianglesFromRoot (E:=E) t) := by
  have hm := triangleFromRoot_measurable (E:=E) t
  exact (hm.preimage (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).inter
    (hm.preimage (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))

/-- The joint probability of two triangles sharing only their root is
the square of the one-triangle probability under iid spherical samples.
Edges belonging to a triangle are not asserted independent. -/
theorem shared_root_triangle_probability (t : ℝ) (a : UnitSphere E) :
    let σ := uniformSphere (volume : Measure E)
    let ν := σ.prod σ
    (σ.prod (ν.prod ν)) (twoTrianglesFromRoot t) =
      ((σ.prod ν) (triangleFromRoot t))^2 := by
  intro σ ν
  let _ : IsProbabilityMeasure σ := uniformSphere_isProbability volume
  let p := ν (triangleAt t a)
  have cond (b : UnitSphere E) : ν (triangleAt t b)=p :=
    triangleAt_measure_root_independent t b a
  have single : (σ.prod ν) (triangleFromRoot t)=p := by
    rw [Measure.prod_apply (triangleFromRoot_measurable t)]
    calc
      _ = ∫⁻ _ : UnitSphere E, p ∂σ := lintegral_congr cond
      _ = p := by simp
  rw [single,Measure.prod_apply (twoTrianglesFromRoot_measurable t)]
  calc
    _ = ∫⁻ _ : UnitSphere E, p^2 ∂σ := by
      apply lintegral_congr
      intro b
      change (ν.prod ν) (triangleAt t b ×ˢ triangleAt t b)=p^2
      rw [Measure.prod_prod,cond,pow_two]
    _ = p^2 := by simp

#print axioms shared_root_triangle_probability
end RobustFolkman
