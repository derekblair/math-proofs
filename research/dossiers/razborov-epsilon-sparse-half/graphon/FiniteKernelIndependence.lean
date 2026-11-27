import FiniteKernelModel
open MeasureTheory Set
open scoped BigOperators
namespace SparseHalfGraphon
variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

theorem uniform_restrict_finset (s : Finset V) (f : V → ℝ) :
    (∫ x in (s : Set V), f x ∂(uniformVertices : Measure V)) =
      (∑ x ∈ s, f x)/(Fintype.card V : ℝ) := by
  rw [← integral_indicator (s.measurableSet), uniform_integral]
  congr 1
  classical
  rw [← Finset.sum_subset (Finset.subset_univ s)
    (f := (s : Set V).indicator f) (fun x _ hx => by simp [hx])]
  exact Finset.sum_congr rfl (fun x hx => by simp [hx])

def IndependentCells (G : V → V → Bool) (s : Set V) : Prop :=
    ∀ u ∈ s, ∀ v ∈ s, G u v = false

theorem finite_independent_iff (G : V → V → Bool) (sym : ∀ u v, G u v = G v u)
    (s : Set V) (pos : 0 < Fintype.card V) :
    (∫ x in s, ∫ y in s, (adjacencyKernel G sym).W (x,y)
      ∂(uniformVertices : Measure V) ∂(uniformVertices : Measure V)) = 0 ↔
      IndependentCells G s := by
  let t := s.toFinite.toFinset
  have ht : (t : Set V) = s := s.toFinite.coe_toFinset
  rw [← ht]
  have A : (∫ x in (t : Set V), ∫ y in (t : Set V), (adjacencyKernel G sym).W (x,y)
      ∂(uniformVertices : Measure V) ∂(uniformVertices : Measure V)) =
    ((∑ x ∈ t, ∑ y ∈ t, edgeReal (G x y))/(Fintype.card V : ℝ)^2) := by
    simp_rw [uniform_restrict_finset]
    simp only [adjacencyKernel,div_eq_mul_inv,Finset.sum_mul,pow_two,mul_inv]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [A]
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast pos.ne'
  rw [div_eq_zero_iff]
  simp only [pow_ne_zero 2 hn,or_false]
  rw [Finset.sum_eq_zero_iff_of_nonneg (by
    intro x _
    exact Finset.sum_nonneg (fun y _ => (adjacencyKernel G sym).nonneg (x,y)))]
  have z (x : V) : (∑ y ∈ t, edgeReal (G x y)) = 0 ↔
      ∀ y ∈ t, edgeReal (G x y) = 0 :=
    Finset.sum_eq_zero_iff_of_nonneg
      (fun y _ => (adjacencyKernel G sym).nonneg (x,y))
  simp_rw [z]
  unfold IndependentCells
  have H (b : Bool) : edgeReal b = 0 ↔ b = false := by cases b <;> norm_num [edgeReal]
  simp only [H,Finset.mem_coe]

theorem finite_alpha_bound_iff (G : V → V → Bool) (sym : ∀ u v, G u v = G v u)
    (pos : 0 < Fintype.card V) (α : ℝ) :
    (∀ s : Finset V, IndependentCells G (s : Set V) →
      (s.card : ℝ)/(Fintype.card V : ℝ) ≤ α) ↔
    (∀ s : Set V, (∫ x in s, ∫ y in s, (adjacencyKernel G sym).W (x,y)
      ∂(uniformVertices : Measure V) ∂(uniformVertices : Measure V)) = 0 →
      (uniformVertices : Measure V).real s ≤ α) := by
  constructor
  · intro h s hs
    let t := s.toFinite.toFinset
    have ht : (t : Set V) = s := s.toFinite.coe_toFinset
    rw [← ht,uniform_finset]
    exact h t (ht ▸ (finite_independent_iff G sym s pos).mp hs)
  · intro h s hs
    rw [← uniform_finset]
    exact h s ((finite_independent_iff G sym s pos).mpr hs)

#print axioms finite_independent_iff
#print axioms finite_alpha_bound_iff
end SparseHalfGraphon
