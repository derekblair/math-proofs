import FiniteKernelHalf
import FiniteKernelPipageInteger
open MeasureTheory Set
open scoped BigOperators
namespace SparseHalfGraphon
open SparseHalfStability
variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
  [MeasurableSpace V] [MeasurableSingletonClass V]

def inducedEdges (G : V → V → Bool) (s : Finset V) : Finset (V × V) :=
  (Edges G).filter (fun e => e.1 ∈ s ∧ e.2 ∈ s)

theorem alloc_edges (G : V → V → Bool) (s : Finset V) :
    edgeCost G (alloc s) = (inducedEdges G s).card := by
  unfold edgeCost inducedEdges
  have hh : (∑ _ ∈ (Edges G).filter (fun e => e.1 ∈ s ∧ e.2 ∈ s), (1:ℝ)) =
      (((Edges G).filter (fun e => e.1 ∈ s ∧ e.2 ∈ s)).card : ℝ) := by simp
  rw [← hh]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases a : e.1 ∈ s <;> by_cases b : e.2 ∈ s <;> simp [alloc,a,b]

theorem form_edges (G : V → V → Bool) (sym : ∀ u v, G u v = G v u)
    (loop : ∀ v, G v v = false) (f : V → ℝ) :
    form (fun v w => edgeReal (G v w)) f f = 2*edgeCost G f := by
  rw [← canonical_cost G f sym loop]
  unfold form orderedCost
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  cases h : G v w <;> simp [edgeReal,h]

theorem edge_scale (G : V → V → Bool) (f : V → ℝ) (n : ℝ) :
    edgeCost G (fun v => f v/n) = edgeCost G f/n^2 := by
  unfold edgeCost
  simp only [div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  rw [← inv_pow]
  ring

theorem round_kernel_half_even (G : V → V → Bool) (sym : ∀ u v, G u v = G v u)
    (loop : ∀ v, G v v = false) (m : ℕ) (even : Fintype.card V = 2*m)
    (H : Half (uniformVertices : Measure V)) (pos : 0 < Fintype.card V) :
    ∃ s : Finset V, s.card = m ∧
      ((inducedEdges G s).card : ℝ)/(Fintype.card V : ℝ)^2 ≤
        halfEnergy uniformVertices (adjacencyKernel G sym) H := by
  have hs := H.mass_half
  rw [uniform_integral] at hs
  have hp : 0 < (Fintype.card V : ℝ) := by exact_mod_cast pos
  have sum := (div_eq_iff hp.ne').mp hs
  have sum' : ∑ v,H.f v = m := by rw [even] at sum; push_cast at sum; linarith
  let A (v w : V) := edgeReal (G v w)
  obtain ⟨s,hcard,hcost⟩ := pipage_integer A
    (fun v w => congrArg edgeReal (sym v w)) (fun v => by simp [A,loop,edgeReal])
    (fun v w => (adjacencyKernel G sym).nonneg (v,w))
    H.f (fun v => ⟨H.nn v,H.le_one v⟩) m sum'
  change form (fun v w => edgeReal (G v w)) (alloc s) (alloc s) ≤
    form (fun v w => edgeReal (G v w)) H.f H.f at hcost
  rw [form_edges G sym loop (alloc s),form_edges G sym loop H.f,alloc_edges] at hcost
  refine ⟨s,hcard,?_⟩
  rw [half_energy_eq_edges G sym loop H, edge_scale]
  exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)

theorem beta_even_ordinary (G : V → V → Bool) (sym : ∀ u v, G u v = G v u)
    (loop : ∀ v, G v v = false) (m : ℕ) (even : Fintype.card V = 2*m)
    (pos : 0 < Fintype.card V) :
    ∃ s : Finset V, s.card = m ∧
      beta uniformVertices (adjacencyKernel G sym) =
        ((inducedEdges G s).card : ℝ)/(Fintype.card V : ℝ)^2 := by
  classical
  let c : Finset V → ℝ := fun s => ((inducedEdges G s).card : ℝ)/(Fintype.card V : ℝ)^2
  let candidates := (Finset.univ : Finset (Finset V)).filter (fun s => s.card=m)
  let H := constantHalf uniformVertices (uniform_mass (V := V) pos)
  obtain ⟨s,hs,-⟩ := round_kernel_half_even G sym loop m even H pos
  have hn : candidates.Nonempty := ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩⟩
  obtain ⟨t,ht,hmin⟩ := Finset.exists_min_image candidates c hn
  have ht' := (Finset.mem_filter.mp ht).2
  refine ⟨t,ht',le_antisymm ?_ ?_⟩
  · let f (v : V) := alloc t v/(Fintype.card V : ℝ)
    have hp : 0 < (Fintype.card V : ℝ) := by exact_mod_cast pos
    have ad (v : V) : 0≤f v ∧ f v≤1/(Fintype.card V : ℝ) := by
      unfold f alloc
      split <;> simp [hp.le]
    have fm : ∑ v, f v = 1/2 := by
      unfold f
      simp only [div_eq_mul_inv,← Finset.sum_mul,sum_alloc,ht']
      rw [← div_eq_mul_inv,div_eq_iff hp.ne',even]
      push_cast
      ring
    let h := finiteHalf f ad fm pos
    have H0 := csInf_le (range_bdd uniformVertices (adjacencyKernel G sym))
      (show halfEnergy uniformVertices (adjacencyKernel G sym) h ∈ _ from ⟨h,rfl⟩)
    have ef : (fun v => h.f v/(Fintype.card V : ℝ)) = f := by
      funext v
      change (Fintype.card V : ℝ)*f v/(Fintype.card V : ℝ)=f v
      field_simp
    rw [half_energy_eq_edges G sym loop h,ef] at H0
    simpa [beta,c,f,edge_scale,alloc_edges] using H0
  · unfold beta
    have hn' : (Set.range (halfEnergy uniformVertices (adjacencyKernel G sym))).Nonempty :=
      ⟨_,⟨H,rfl⟩⟩
    apply le_csInf hn' 
    rintro x ⟨h,rfl⟩
    obtain ⟨s,hs,he⟩ := round_kernel_half_even G sym loop m even h pos
    exact (hmin s (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩)).trans he

#print axioms round_kernel_half_even
#print axioms beta_even_ordinary
end SparseHalfGraphon
