import HighMarkFinite
open MeasureTheory Set Function
open scoped BigOperators
namespace SparseHalfGraphon
variable {X V : Type*} [MeasurableSpace X] [Fintype V]
  [MeasurableSpace V] [MeasurableSingletonClass V]

/-- A pointwise independent set in a pulled finite adjacency graph is
bounded by the true finite alpha. This also permits fractional splits
of a vertex fiber inside the common coupling space. -/
theorem finite_pull_independent_cap (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → V) (hp : MeasurePreserving p μ uniformVertices) (G : V → V → Bool)
    (α : ℝ) (cap : ∀ s : Finset V, IndependentCells G (s : Set V) →
      (s.card : ℝ)/(Fintype.card V : ℝ) ≤ α)
    (S : Set X) (hS : ∀ x ∈ S, ∀ y ∈ S, G (p x) (p y) = false) :
    μ.real S ≤ α := by
  let T := p '' S
  have hT : MeasurableSet T := T.toFinite.measurableSet
  let t := T.toFinite.toFinset
  have eq : (t : Set V) = T := T.toFinite.coe_toFinset
  have ht : IndependentCells G T := by
    intro a ha b hb
    obtain ⟨x,hx,rfl⟩ := ha
    obtain ⟨y,hy,rfl⟩ := hb
    exact hS x hx y hy
  have H := cap t (eq ▸ ht)
  rw [← uniform_finset,eq] at H
  exact (measureReal_mono (show S ⊆ p ⁻¹' T from fun x hx => ⟨x,hx,rfl⟩)).trans
    ((real_mass_pull hp hT).trans_le H)

variable (μ : Measure X) [IsFiniteMeasure μ]

private theorem binary_row (K : Kernel X) (G : X → X → Bool)
    (hK : ∀ x y, K.W (x,y)=edgeReal (G x y)) (x : X) (S : Set X) :
    deg (μ.restrict S) K x = μ.real (markedNeighbor G S x) := by
  let D := {w | G x w = true}
  have md : MeasurableSet D := by
    have E : D = (fun w => K.W (x,w)) ⁻¹' ({1} : Set ℝ) := by
      ext w
      change (G x w = true) ↔ K.W (x,w) = 1
      rw [hK]
      cases h : G x w <;> norm_num [edgeReal]
    rw [E]
    exact rowMeasurable K x (measurableSet_singleton _)
  have he : (fun w => K.W (x,w)) = D.indicator (fun _ => (1:ℝ)) := by
    funext w
    by_cases h : G x w = true <;> simp [D,hK,edgeReal,h]
  unfold deg
  rw [he,integral_indicator md,Measure.restrict_restrict md,inter_comm]
  simp [markedNeighbor,setIntegral_const,smul_eq_mul,D,Set.ofPred_and]

/-- Two rows whose total degree into one anchor exceeds its mass
cannot be adjacent in a pointwise triangle-free binary kernel. -/
theorem aligned_forbidden_edge (K : Kernel X) (G : X → X → Bool)
    (hK : ∀ x y, K.W (x,y)=edgeReal (G x y))
    (tf : ∀ u v w, G u v=true → G u w=true → G v w=false)
    (S : Set X) (mS : MeasurableSet S) (x y : X)
    (large : μ.real S < deg (μ.restrict S) K x + deg (μ.restrict S) K y) :
    G x y = false := by
  by_contra h
  have e : G x y = true := by simpa using h
  have hd : Disjoint (markedNeighbor G S x) (markedNeighbor G S y) := by
    apply disjoint_left.mpr
    intro w hx hy
    exact Bool.noConfusion ((tf x y w e hx.2).symm.trans hy.2)
  have mU : MeasurableSet (markedNeighbor G S y) := by
    change MeasurableSet (S ∩ {w | G y w=true})
    apply mS.inter
    have E : {w | G y w=true} = (fun w => K.W (y,w)) ⁻¹' ({1}:Set ℝ) := by
      ext w
      change (G y w=true) ↔ K.W (y,w)=1
      rw [hK]
      cases h : G y w <;> norm_num [edgeReal]
    rw [E]
    exact rowMeasurable K y (measurableSet_singleton _)
  have hu : μ.real (markedNeighbor G S x ∪ markedNeighbor G S y) ≤ μ.real S :=
    measureReal_mono (fun _ hz => hz.elim And.left And.left)
  rw [measureReal_union hd mU,← binary_row μ K G hK,← binary_row μ K G hK] at hu
  exact (not_lt_of_ge hu) large

theorem active_pull_cap (p : X → V) (hp : MeasurePreserving p μ uniformVertices)
    (G : V → V → Bool) (sym : ∀ u v, G u v=G v u)
    (tf : ∀ u v w, G u v=true → G u w=true → G v w=false)
    (α : ℝ) (cap : ∀ s : Finset V, IndependentCells G (s : Set V) →
      (s.card : ℝ)/(Fintype.card V : ℝ) ≤ α)
    (S Q U T : Set X) (hS : MeasurableSet S) (hQ : MeasurableSet Q)
    (mT : MeasurableSet T) (dis : Disjoint U T)
    (hT : ∀ x ∈ T, ∀ y ∈ T, G (p x) (p y)=false)
    (ε : ℝ)
    (hU : ∀ x ∈ U, μ.real S/2 < deg (μ.restrict S)
      (pullKernel (adjacencyKernel G sym) p hp.measurable) x)
    (hUQ : ∀ x ∈ U, ε < deg (μ.restrict Q)
      (pullKernel (adjacencyKernel G sym) p hp.measurable) x)
    (hTQ : ∀ x ∈ T, μ.real Q-ε < deg (μ.restrict Q)
      (pullKernel (adjacencyKernel G sym) p hp.measurable) x) :
    μ.real U+μ.real T ≤ α := by
  rw [← measureReal_union dis mT]
  apply finite_pull_independent_cap μ p hp G α cap
  let K := pullKernel (adjacencyKernel G sym) p hp.measurable
  let A (x y : X) := G (p x) (p y)
  have e (x y : X) : K.W (x,y)=edgeReal (A x y) := rfl
  have ft (u v w : X) := tf (p u) (p v) (p w)
  intro x hx y hy
  rcases hx with hx|hx <;> rcases hy with hy|hy
  · apply aligned_forbidden_edge μ K A e ft S hS x y
    linarith [hU x hx,hU y hy]
  · apply aligned_forbidden_edge μ K A e ft Q hQ x y
    linarith [hUQ x hx,hTQ y hy]
  · rw [sym (p x) (p y)]
    apply aligned_forbidden_edge μ K A e ft Q hQ y x
    linarith [hUQ y hy,hTQ x hx]
  · exact hT x hx y hy

#print axioms finite_pull_independent_cap
#print axioms active_pull_cap
end SparseHalfGraphon
