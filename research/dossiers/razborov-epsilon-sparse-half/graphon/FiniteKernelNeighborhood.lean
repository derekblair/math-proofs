import FiniteKernelIndependence
open MeasureTheory Set
open scoped BigOperators
namespace SparseHalfGraphon
variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

def finiteNeighborhood (G : V → V → Bool) (v : V) : Finset V :=
  Finset.univ.filter (fun w => G v w = true)

theorem finite_neighborhood_independent (G : V → V → Bool)
    (tf : ∀ u v w, G u v = true → G u w = true → G v w = false) (v : V) :
    IndependentCells G (finiteNeighborhood G v : Set V) := by
  intro u hu w hw
  exact tf v u w (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hw).2

theorem finite_neighborhood_mass (G : V → V → Bool) (sym : ∀ u v, G u v = G v u) (v : V) :
    (uniformVertices : Measure V).real (finiteNeighborhood G v : Set V) =
      deg uniformVertices (adjacencyKernel G sym) v := by
  rw [uniform_finset,degree_finite]
  rfl

theorem finite_degree_le_alpha (G : V → V → Bool) (sym : ∀ u v, G u v = G v u)
    (tf : ∀ u v w, G u v = true → G u w = true → G v w = false)
    (α : ℝ) (bound : ∀ s : Finset V, IndependentCells G (s : Set V) →
      (s.card : ℝ)/(Fintype.card V : ℝ) ≤ α) :
    ∀ v, deg uniformVertices (adjacencyKernel G sym) v ≤ α := by
  intro v
  rw [← finite_neighborhood_mass G sym v,uniform_finset]
  exact bound _ (finite_neighborhood_independent G tf v)

#print axioms finite_degree_le_alpha
end SparseHalfGraphon
