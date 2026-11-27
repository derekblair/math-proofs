import GeometricUniformSphere
import GeometricCompact
import Mathlib.Analysis.InnerProductSpace.GramMatrix

namespace RobustFolkman
open MeasureTheory Set Finset Matrix
open scoped InnerProductSpace
variable {V I E : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [Fintype V] in
private theorem pair_eq_or {a b u v : V} (ab : a≠b)
    (h : ({a,b}:Finset V)={u,v}) : (a=u ∧ b=v) ∨ (a=v ∧ b=u) := by
  have x : a=u ∨ a=v := by
    have : a∈({u,v}:Finset V) := h ▸ (by simp)
    simpa using this
  have y : b=u ∨ b=v := by
    have : b∈({u,v}:Finset V) := h ▸ (by simp)
    simpa using this
  grind

theorem pointGraph_hasEdge (t : ℝ) (x : V→UnitSphere E) (a b : V) :
    hasEdge (pointGraph t x) a b ↔ a≠b ∧ t≤⟪(x a:E),(x b:E)⟫_ℝ := by
  classical
  constructor
  · rintro ⟨ab,m⟩
    obtain ⟨⟨u,v⟩,uv,eq⟩ := mem_image.mp m
    obtain ⟨_,_,edge⟩ := mem_filter.mp uv
    refine ⟨ab,?_⟩
    rcases pair_eq_or ab eq.symm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact edge
    · rwa [real_inner_comm]
  · rintro ⟨ab,e⟩
    exact ⟨ab,mem_image.mpr ⟨(a,b),mem_filter.mpr ⟨mem_univ _,ab,e⟩,rfl⟩⟩

noncomputable def pointGram (x : I→UnitSphere E) : Matrix I I ℝ :=
  Matrix.gram ℝ (fun i => (x i:E))

theorem pointGram_diag (x : I→UnitSphere E) (i : I) : pointGram x i i=1 := by
  change ⟪(x i:E),(x i:E)⟫_ℝ=1
  have h : ‖(x i:E)‖=1 := by
    simpa [Metric.mem_sphere,dist_zero_right] using (x i).property
  rw [real_inner_self_eq_norm_sq,h,one_pow]

def labeledPattern (C : I→I→Prop) (lab : I ↪ V) (g : EdgeGraph V) : Prop :=
  ∀ i j, C i j → hasEdge g (lab i) (lab j)

/-- On any injectively labeled vertex set, the prescribed non-induced
graph pattern is exactly the stated unit-diagonal Gram event. -/
theorem point_pattern_iff_gram (C : I→I→Prop) (noloop : ∀ i, ¬C i i)
    (lab : I ↪ V) (t : ℝ) (x : V→UnitSphere E) :
    labeledPattern C lab (pointGraph t x) ↔ GeometricGap.GramFeasible C t (pointGram (x∘lab)) := by
  constructor
  · intro h
    refine ⟨Matrix.posSemidef_gram ℝ _,pointGram_diag _,?_⟩
    intro i j e
    exact ((pointGraph_hasEdge t x _ _).mp (h i j e)).2
  · intro h i j e
    refine (pointGraph_hasEdge t x _ _).mpr ⟨?_,h.2.2 i j e⟩
    intro eq
    exact noloop i ((lab.injective eq).symm ▸ e)

/-- The actual random graph law of a fixed pattern is the actual Gram
event for the selected time-independent distinct labels, with no
hypothesis that different edges are independent. -/
theorem point_pattern_probability (μ : Measure (V→UnitSphere E)) [IsProbabilityMeasure μ]
    (C : I→I→Prop) (noloop : ∀ i, ¬C i i) (lab : I ↪ V) (t : ℝ)
    [DecidablePred (labeledPattern C lab)] :
    (∑ g : EdgeGraph V, if labeledPattern C lab g then finiteGraphMass μ (pointGraph t) g else 0)=
      (μ {x | GeometricGap.GramFeasible C t (pointGram (x∘lab))}).toReal := by
  rw [finiteGraphMass_event μ (pointGraph t) (measurable_pointGraph_fiber t)]
  congr 2
  ext x
  exact point_pattern_iff_gram C noloop lab t x

#print axioms point_pattern_probability
end RobustFolkman
