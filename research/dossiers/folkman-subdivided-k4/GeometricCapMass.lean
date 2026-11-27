import GeometricRootCap

namespace RobustFolkman.GeometricGap
open MeasureTheory Matrix Set
open scoped ENNReal InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem capPoints_edge_mass (t : ℝ) (a : UnitSphere E) :
    let σ := uniformSphere (volume : Measure E)
    patternMass (E:=E) edgeCon t=σ (capPoints t a) := by
  classical
  intro σ
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  let S : Set (UnitSphere E×UnitSphere E) := {p | p.2∈capPoints t p.1}
  have Sm : MeasurableSet S := by
    change MeasurableSet {p : UnitSphere E×UnitSphere E | t≤⟪(p.1:E),(p.2:E)⟫_ℝ}
    exact measurableSet_le measurable_const
      ((continuous_subtype_val.comp continuous_fst).inner (𝕜:=ℝ)
        (continuous_subtype_val.comp continuous_snd)).measurable
  let f := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitSphere E)
  have p := measurePreserving_piFinTwo (fun _ : Fin 2 => σ)
  have pr : f⁻¹' S = {x | GramFeasible edgeCon t (pointGram x)} := by
    ext x
    change t≤⟪(x 0:E),(x 1:E)⟫_ℝ ↔ GramFeasible edgeCon t (pointGram x)
    constructor
    · intro h
      refine ⟨Matrix.posSemidef_gram ℝ _,pointGram_diag _,?_⟩
      intro i j hn
      fin_cases i <;> fin_cases j
      · exact False.elim (hn rfl)
      · exact h
      · change t≤⟪(x 1:E),(x 0:E)⟫_ℝ
        rwa [real_inner_comm]
      · exact False.elim (hn rfl)
    · exact fun h => h.2.2 0 1 (by simp [edgeCon])
  have q := p.measure_preimage Sm.nullMeasurableSet
  change (Measure.pi fun _ : Fin 2 => σ) (f ⁻¹' S)=(σ.prod σ) S at q
  rw [pr] at q
  change patternMass (E:=E) edgeCon t = (σ.prod σ) S at q
  rw [q,Measure.prod_apply Sm]
  calc
    _ = ∫⁻ _ : UnitSphere E, σ (capPoints t a) ∂σ := by
      apply lintegral_congr
      intro z
      exact capPoints_mass_root_constant t z a
    _ = _ := by simp

#print axioms capPoints_edge_mass
end RobustFolkman.GeometricGap
