import GeometricPatternMeasure

namespace RobustFolkman
open MeasureTheory Set
variable {V I X E : Type*} [Fintype V] [Fintype I] [MeasurableSpace X]

/-- Any distinct choice of coordinates of an iid product is again
an iid product, in the labeled order. -/
theorem pi_embedding_measurePreserving (σ : Measure X) [IsProbabilityMeasure σ]
    (lab : I ↪ V) :
    MeasurePreserving (fun x : V→X => fun i => x (lab i))
      (Measure.pi fun _ : V => σ) (Measure.pi fun _ : I => σ) := by
  classical
  let P := Set.range lab
  let _ : Fintype P := Subtype.fintype (fun i => i∈P)
  let e : I ≃ P := Equiv.ofInjective lab lab.injective
  let s := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : V => X) (fun i => i∈P)
  let r := MeasurableEquiv.piCongrLeft (fun _ : I => X) e.symm
  have f : MeasurePreserving s (Measure.pi fun _ : V => σ)
      ((Measure.pi fun _ : P => σ).prod (Measure.pi fun _ : ↥Pᶜ => σ)) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : V => σ) (fun i => i∈P)
  have proj : MeasurePreserving Prod.fst
      ((Measure.pi fun _ : P => σ).prod (Measure.pi fun _ : ↥Pᶜ => σ))
      (Measure.pi fun _ : P => σ) := measurePreserving_fst
  have rr : MeasurePreserving r (Measure.pi fun _ : P => σ) (Measure.pi fun _ : I => σ) :=
    measurePreserving_piCongrLeft (fun _ : I => σ) e.symm
  convert rr.comp (proj.comp f) using 1
  funext x i
  have q := MeasurableEquiv.piCongrLeft_apply_apply e.symm (β:=fun _ => X) (s x).1 (e i)
  rw [Equiv.symm_apply_apply] at q
  exact q.symm

variable [DecidableEq V] [DecidableEq I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem continuous_pointGram : Continuous (pointGram (I:=I) (E:=E)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_subtype_val.comp (continuous_apply i)).inner
    (continuous_subtype_val.comp (continuous_apply j))

theorem point_pattern_probability_iid (σ : Measure (UnitSphere E)) [IsProbabilityMeasure σ]
    (C : I→I→Prop) (noloop : ∀ i, ¬C i i) (lab : I ↪ V) (t : ℝ)
    [DecidablePred (labeledPattern C lab)] :
    let μ := Measure.pi fun _ : V => σ
    (∑ g : EdgeGraph V, if labeledPattern C lab g then finiteGraphMass μ (pointGraph t) g else 0)=
      ((Measure.pi fun _ : I => σ) {y | GeometricGap.GramFeasible C t (pointGram y)}).toReal := by
  intro μ
  rw [point_pattern_probability μ C noloop lab t]
  let U : Set (I→UnitSphere E) := {y | GeometricGap.GramFeasible C t (pointGram y)}
  have Umeas : MeasurableSet U :=
    ((GeometricGap.closed_gram_feasible C t).preimage continuous_pointGram).measurableSet
  have m := (pi_embedding_measurePreserving σ lab).measure_preimage Umeas.nullMeasurableSet
  exact congrArg ENNReal.toReal m

#print axioms point_pattern_probability_iid
end RobustFolkman
