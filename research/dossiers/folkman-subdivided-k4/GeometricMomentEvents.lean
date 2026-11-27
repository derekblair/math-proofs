import GeometricLabelShapes
import GeometricMarginals

namespace RobustFolkman.GeometricGap
open MeasureTheory Matrix Set
open scoped ENNReal
variable {V I E : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

noncomputable def sphericalHostWeight (t : ℝ) (g : EdgeGraph V) : ℝ :=
  finiteGraphMass
    (Measure.pi fun _ : V => uniformSphere (volume : Measure E)) (pointGraph t) g

noncomputable def labeledIndicator (C : I→I→Prop) (l : I↪V) (g : EdgeGraph V) : ℝ :=
  by classical exact if labeledPattern C l g then 1 else 0

theorem sphericalHostWeight_probability (t : ℝ) :
    (∀ g : EdgeGraph V, 0≤sphericalHostWeight (E:=E) t g) ∧
    (∑ g : EdgeGraph V, sphericalHostWeight (E:=E) t g)=1 := by
  let σ := uniformSphere (volume : Measure E)
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  exact finite_spherical_graph_law (V:=V) σ t

theorem labeled_moment_probability (C : I→I→Prop) (noloop : ∀ i, ¬C i i)
    (l : I↪V) (t : ℝ) :
    Moment.mean (sphericalHostWeight (E:=E) t) (labeledIndicator C l) =
      (patternMass (E:=E) C t).toReal := by
  classical
  let σ := uniformSphere (volume : Measure E)
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  unfold Moment.mean
  have eq (g : EdgeGraph V) : sphericalHostWeight (E:=E) t g * labeledIndicator C l g =
      if labeledPattern C l g then sphericalHostWeight (E:=E) t g else 0 := by
    by_cases h : labeledPattern C l g <;> simp [labeledIndicator,h]
  simp_rw [eq]
  exact point_pattern_probability_iid σ C noloop l t

theorem page_noloop {J : Type*} (C : J→J→Prop) (nl : ∀ i, ¬C i i) (a b : J) :
    ∀ i, ¬pageEdges C a b i i := by
  intro i
  rcases i with i|i
  · exact nl i
  · exact not_false

theorem diamond_noloop : ∀ i, ¬diamondEdges i i := by
  intro i
  rcases i with i|i
  · exact fun h => h rfl
  · exact not_false

theorem triangle_noloop : ∀ i, ¬triangleCon i i := page_noloop edgeCon (fun _ h => h rfl) _ _
theorem forbidden_noloop : ∀ i, ¬subEdges i i := page_noloop diamondEdges diamond_noloop _ _
theorem extension_noloop : ∀ i, ¬extCon i i := page_noloop subEdges forbidden_noloop _ _

#print axioms labeled_moment_probability
end RobustFolkman.GeometricGap
