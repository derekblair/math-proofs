import GeometricFailurePowers
import GeometricRateWindow

namespace RobustFolkman.GeometricGap
open MeasureTheory Matrix Set
open scoped ENNReal

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gramFeasible_reindex (e : J≃I) (C : I→I→Prop) (t : ℝ) (A : Matrix I I ℝ) :
    GramFeasible (fun i j => C (e i) (e j)) t (A.submatrix e e) ↔ GramFeasible C t A := by
  constructor
  · intro p
    refine ⟨(posSemidef_submatrix_equiv e).mp p.1,?_,?_⟩
    · intro i
      simpa using p.2.1 (e.symm i)
    · intro i j h
      have h1 : C (e (e.symm i)) (e (e.symm j)) := by simpa using h
      simpa using p.2.2 (e.symm i) (e.symm j) h1
  · intro p
    exact ⟨p.1.submatrix _,fun i => p.2.1 _,fun i j => p.2.2 _ _⟩

theorem gramOptimal_reindex (e : J≃I) (C : I→I→Prop) (t : ℝ) (A : Matrix I I ℝ)
    (o : GramOptimal C t A) :
    GramOptimal (fun i j => C (e i) (e j)) t (A.submatrix e e) := by
  refine ⟨(gramFeasible_reindex e C t A).mpr o.1,?_⟩
  intro B b
  let U := B.submatrix e.symm e.symm
  have sub : U.submatrix e e=B := by ext i j; simp [U]
  have u : GramFeasible C t U := (gramFeasible_reindex e C t U).mp (sub ▸ b)
  have le := o.2 U u
  rw [Matrix.det_submatrix_equiv_self]
  simpa [U,Matrix.det_submatrix_equiv_self] using le

noncomputable def patternMass (C : I→I→Prop) (t : ℝ) : ℝ≥0∞ :=
  (Measure.pi fun _ : I => uniformSphere (volume : Measure E))
    {v | GramFeasible C t (pointGram v)}

theorem gramEvent_measurable (C : I→I→Prop) (t : ℝ) :
    MeasurableSet {v : I→UnitSphere E | GramFeasible C t (pointGram v)} := by
  have p : Continuous (pointGram (I:=I) (E:=E)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (continuous_subtype_val.comp (continuous_apply i)).inner
      (continuous_subtype_val.comp (continuous_apply j))
  exact ((closed_gram_feasible C t).preimage p).measurableSet

theorem patternMass_reindex (e : J≃I) (C : I→I→Prop) (t : ℝ) :
    patternMass (E:=E) (fun i j => C (e i) (e j)) t = patternMass (E:=E) C t := by
  let σ := uniformSphere (volume : Measure E)
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  let P := MeasurableEquiv.piCongrLeft (fun _ : J => UnitSphere E) e.symm
  have p := measurePreserving_piCongrLeft (fun _ : J => σ) e.symm
  let s : Set (J→UnitSphere E) := {v | GramFeasible (fun i j => C (e i) (e j)) t (pointGram v)}
  have ms : MeasurableSet s := gramEvent_measurable _ _
  change (Measure.pi fun _ : J => σ) s =
    (Measure.pi fun _ : I => σ) {v | GramFeasible C t (pointGram v)}
  rw [← p.measure_preimage ms.nullMeasurableSet]
  congr 1
  ext v
  change GramFeasible (fun i j => C (e i) (e j)) t (pointGram (P v)) ↔ _
  have eq : pointGram (P v) = (pointGram v).submatrix e e := by
    ext i j
    simp [P,pointGram,Matrix.submatrix_apply,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft]
  rw [eq,gramFeasible_reindex]
  rfl

#print axioms patternMass_reindex
end RobustFolkman.GeometricGap
