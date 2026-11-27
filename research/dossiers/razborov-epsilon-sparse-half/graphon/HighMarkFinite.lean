import FiniteKernelIndependence
import MarkedLimits
open MeasureTheory Set Function
open scoped BigOperators
namespace SparseHalfGraphon
variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

def markedNeighbor (G : V → V → Bool) (A : Set V) (v : V) : Set V :=
  {w | w ∈ A ∧ G v w = true}

theorem deg_adjacency_restrict (μ : Measure V) [IsFiniteMeasure μ]
    (G : V → V → Bool) (sym : ∀ u v, G u v=G v u) (A : Set V) (v : V) :
    deg (μ.restrict A) (adjacencyKernel G sym) v = μ.real (markedNeighbor G A v) := by
  have hm : MeasurableSet (markedNeighbor G A v) := (markedNeighbor G A v).toFinite.measurableSet
  have ha : MeasurableSet A := A.toFinite.measurableSet
  have he : (fun w => (adjacencyKernel G sym).W (v,w)) =
      ({w | G v w = true} : Set V).indicator (fun _ => (1:ℝ)) := by
    funext w
    change edgeReal (G v w) = _
    by_cases h : G v w = true <;> simp [edgeReal,h]
  unfold deg
  rw [he,integral_indicator (({w | G v w = true} : Set V).toFinite.measurableSet)]
  rw [Measure.restrict_restrict (({w | G v w = true} : Set V).toFinite.measurableSet)]
  change (∫ x in {w | G v w = true} ∩ A, (1:ℝ) ∂μ) = _
  rw [inter_comm]
  simp [markedNeighbor,setIntegral_const,smul_eq_mul,Set.setOf_and]

def highOutside (μ : Measure V) [IsFiniteMeasure μ] (K : Kernel V) (A : Set V) (t : ℝ) : Set V :=
  {v | v ∉ A ∧ t < deg (μ.restrict A) K v}

theorem highOutside_independent (μ : Measure V) [IsFiniteMeasure μ]
    (G : V → V → Bool) (sym : ∀ u v, G u v=G v u)
    (tf : ∀ u v w, G u v=true → G u w=true → G v w=false) (A : Set V) :
    IndependentCells G (highOutside μ (adjacencyKernel G sym) A (μ.real A/2)) := by
  intro u hu v hv
  by_contra hg
  have g : G u v = true := by simpa using hg
  have Hd : Disjoint (markedNeighbor G A u) (markedNeighbor G A v) := by
    apply Set.disjoint_left.mpr
    intro z hu hv
    have ha : G u z = true := hu.2
    have hb : G v z = true := hv.2
    exact Bool.noConfusion ((tf u v z g ha).symm.trans hb)
  have hM : μ.real (markedNeighbor G A u) + μ.real (markedNeighbor G A v) ≤ μ.real A := by
    rw [← measureReal_union Hd (markedNeighbor G A v).toFinite.measurableSet]
    exact measureReal_mono (fun x h => h.elim And.left And.left)
  have hu' := hu.2
  have hv' := hv.2
  rw [deg_adjacency_restrict μ G sym A u] at hu'
  rw [deg_adjacency_restrict μ G sym A v] at hv'
  linarith

theorem finite_highOutside_cap
    (G : V → V → Bool) (sym : ∀ u v, G u v=G v u)
    (tf : ∀ u v w, G u v=true → G u w=true → G v w=false) (A : Set V)
    (α : ℝ)
    (cap : ∀ s : Finset V, IndependentCells G (s : Set V) →
      (s.card : ℝ)/(Fintype.card V : ℝ) ≤ α) :
    (uniformVertices : Measure V).real
      (highOutside uniformVertices (adjacencyKernel G sym) A ((uniformVertices : Measure V).real A/2))
      ≤ α := by
  let S := highOutside uniformVertices (adjacencyKernel G sym) A ((uniformVertices : Measure V).real A/2)
  let t := S.toFinite.toFinset
  have he : (t : Set V) = S := S.toFinite.coe_toFinset
  change (uniformVertices : Measure V).real S ≤ α
  rw [← he,uniform_finset]
  apply cap t
  rw [he]
  exact highOutside_independent uniformVertices G sym tf A

#print axioms finite_highOutside_cap
end SparseHalfGraphon
