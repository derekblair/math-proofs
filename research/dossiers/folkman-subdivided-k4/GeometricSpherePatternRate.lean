import GeometricJointGramNormalized
import GeometricPatternMeasure

namespace RobustFolkman.GeometricGap
open MeasureTheory Matrix Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

noncomputable def spherePatternMass (C : Fin n→Fin n→Prop) (t : ℝ) : ℝ≥0∞ :=
  (Measure.pi (fun _ : Fin n => uniformSphere (volume : Measure E)))
    {v | GramFeasible C t (pointGram v)}

theorem chartWeight_full_integral (n m : ℕ) :
    (∫⁻ x, chartWeight n m x) =
      ∫⁻ x in chartRegion (I:=Fin n) (fun _ _ => False) (1/40000), chartWeight n m x := by
  let s := chartRegion (I:=Fin n) (fun _ _ => False) (1/40000)
  have h : MeasurableSet s := (chartRegion_compact (I:=Fin n) _ _).measurableSet
  change _ = ∫⁻ x in s, chartWeight n m x
  rw [← lintegral_indicator h]
  apply lintegral_congr
  intro x
  by_cases H : x∈s
  · rw [indicator_of_mem H]
  · rw [indicator_of_notMem H]
    apply indicator_of_notMem
    intro pd
    apply H
    exact ⟨(show (gramChart x).PosDef from pd).posSemidef,gramChart_diag x,fun _ _ h => h.elim⟩

theorem sphere_pattern_mass_integrals (n m : ℕ) (hm : 0<m)
    (dim : Module.finrank ℝ E=n+m+1) (C : Fin n→Fin n→Prop) (t : ℝ) :
    spherePatternMass (E:=E) C t =
    patternIntegral C t ((m:ℝ)/2) /
      patternIntegral (I:=Fin n) (fun _ _ => False) (1/40000) ((m:ℝ)/2) := by
  let s := chartRegion C t
  have hs : MeasurableSet s := (chartRegion_compact C t).measurableSet
  have law := spherical_joint_gram_normalized (E:=E) n m dim
    (s.indicator (fun _ => 1)) (measurable_const.indicator hs)
  rw [lintegral_indicator_const_comp sampleChart_measurable hs 1,one_mul] at law
  have eq : sampleChart ⁻¹' s = {v : Fin n→UnitSphere E | GramFeasible C t (pointGram v)} := by
    ext v
    change GramFeasible C t (gramChart (sampleChart v)) ↔ GramFeasible C t (pointGram v)
    rw [sampleChart_matrix]
    rfl
  rw [eq,chartWeight_full_integral] at law
  have A : (∫⁻ x, chartWeight n m x*s.indicator (fun _ => (1:ℝ≥0∞)) x) =
      ∫⁻ x in s, chartWeight n m x := by
    rw [← lintegral_indicator hs]
    apply lintegral_congr
    intro x
    by_cases h : x∈s <;> simp [indicator_of_mem,indicator_of_notMem,h]
  rw [A,chart_integral_weighted_event _ _ hm,chart_integral_weighted_event _ _ hm] at law
  exact law

#print axioms sphere_pattern_mass_integrals
end RobustFolkman.GeometricGap
