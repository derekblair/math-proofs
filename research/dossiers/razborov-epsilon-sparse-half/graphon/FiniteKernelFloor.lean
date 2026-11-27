import FiniteKernelEven
open MeasureTheory Set
open scoped BigOperators
namespace SparseHalfGraphon
open SparseHalfStability
variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
  [MeasurableSpace V] [MeasurableSingletonClass V]

theorem round_kernel_half_floor (G : V → V → Bool) (sym : ∀ u v, G u v = G v u)
    (loop : ∀ v, G v v = false) (H : Half (uniformVertices : Measure V))
    (pos : 0 < Fintype.card V) :
    ∃ s : Finset V, s.card = Fintype.card V / 2 ∧
      ((inducedEdges G s).card : ℝ)/(Fintype.card V : ℝ)^2 ≤
        halfEnergy uniformVertices (adjacencyKernel G sym) H := by
  let n := Fintype.card V
  let m := n/2
  have np : 0 < (n : ℝ) := by dsimp [n]; exact_mod_cast pos
  have hm : ((m : ℝ)*2) ≤ n := by
    have hh : m*2 ≤ n := by dsimp [m]; omega
    exact_mod_cast hh
  let t : ℝ := (m : ℝ)/((n : ℝ)/2)
  have ht0 : 0 ≤ t := div_nonneg (Nat.cast_nonneg _) (by positivity)
  have ht1 : t ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ)/2)).mpr
    linarith
  let x (v : V) := t*H.f v
  have bx (v : V) : 0≤x v ∧ x v≤1 := by
    refine ⟨mul_nonneg ht0 (H.nn v),?_⟩
    change t*H.f v≤1
    simpa using mul_le_mul ht1 (H.le_one v) (H.nn v) (by norm_num : (0:ℝ)≤1)
  have hs := H.mass_half
  rw [uniform_integral] at hs
  have sum : (∑ v,H.f v) = (n : ℝ)/2 := by
    have eq := (div_eq_iff np.ne').mp hs
    linarith
  have xm : (∑ v,x v) = m := by
    simp only [x,← Finset.mul_sum,sum,t]
    field_simp
  let A (v w : V) := edgeReal (G v w)
  obtain ⟨s,cs,cost⟩ := pipage_integer A (fun v w => congrArg edgeReal (sym v w))
    (fun v => by simp [A,loop,edgeReal]) (fun v w => (adjacencyKernel G sym).nonneg (v,w))
    x bx m xm
  have mono : form A x x ≤ form A H.f H.f := by
    unfold form
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro b _
    have h (v : V) : x v≤H.f v := by
      simpa [x] using mul_le_mul_of_nonneg_right ht1 (H.nn v)
    exact mul_le_mul (mul_le_mul_of_nonneg_left (h a) ((adjacencyKernel G sym).nonneg (a,b)))
      (h b) (bx b).1 (mul_nonneg ((adjacencyKernel G sym).nonneg (a,b)) (H.nn a))
  have c := cost.trans mono
  change form (fun v w => edgeReal (G v w)) (alloc s) (alloc s) ≤
    form (fun v w => edgeReal (G v w)) H.f H.f at c
  rw [form_edges G sym loop (alloc s),form_edges G sym loop H.f,alloc_edges] at c
  refine ⟨s,cs,?_⟩
  rw [half_energy_eq_edges G sym loop H,edge_scale]
  exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)

theorem ordinary_floor_le_beta (G : V → V → Bool) (sym : ∀ u v, G u v = G v u)
    (loop : ∀ v, G v v = false) (pos : 0 < Fintype.card V) :
    ∃ s : Finset V, s.card = Fintype.card V / 2 ∧
      ((inducedEdges G s).card : ℝ)/(Fintype.card V : ℝ)^2 ≤
        beta uniformVertices (adjacencyKernel G sym) := by
  classical
  let c : Finset V → ℝ := fun s => ((inducedEdges G s).card : ℝ)/(Fintype.card V : ℝ)^2
  let candidates := (Finset.univ : Finset (Finset V)).filter (fun s => s.card=Fintype.card V/2)
  let H := constantHalf uniformVertices (uniform_mass (V := V) pos)
  obtain ⟨s,hs,-⟩ := round_kernel_half_floor G sym loop H pos
  have hn : candidates.Nonempty := ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩⟩
  obtain ⟨t,ht,hmin⟩ := Finset.exists_min_image candidates c hn
  refine ⟨t,(Finset.mem_filter.mp ht).2,?_⟩
  unfold beta
  have hn' : (Set.range (halfEnergy uniformVertices (adjacencyKernel G sym))).Nonempty :=
    ⟨_,⟨H,rfl⟩⟩
  apply le_csInf hn'
  rintro _ ⟨h,rfl⟩
  obtain ⟨s,hs,he⟩ := round_kernel_half_floor G sym loop h pos
  exact (hmin s (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩)).trans he

#print axioms round_kernel_half_floor
#print axioms ordinary_floor_le_beta
end SparseHalfGraphon
