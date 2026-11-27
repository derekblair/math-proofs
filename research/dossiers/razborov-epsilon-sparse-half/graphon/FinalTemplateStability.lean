import FinalBinaryTransfer

open MeasureTheory Set Filter Topology
open scoped BigOperators
namespace SparseHalfGraphon
open SparseHalfStability

def petersenBaseAdj (a b : Fin 10) : Bool := PetersenStability.adj (pEmbed a) (pEmbed b)

theorem petersenBaseAdj_sym : ∀ a b, petersenBaseAdj a b = petersenBaseAdj b a := by decide
theorem petersenBaseAdj_loopless : ∀ a, petersenBaseAdj a a = false := by decide
theorem c5BaseAdj_sym : ∀ a b : Fin 5, C5Stability.adj a b = C5Stability.adj b a := by decide
theorem c5BaseAdj_loopless : ∀ a : Fin 5, C5Stability.adj a a = false := by decide

section
variable {V : ℕ→Type*}
    [∀ k, Fintype (V k)] [∀ k, MeasurableSpace (V k)] [∀ k, MeasurableSingletonClass (V k)]
    [deq : ∀ k, DecidableEq (V k)] [ord : ∀ k, LinearOrder (V k)]
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    (G : ∀ k, V k→V k→Bool) (sym : ∀ k u v, G k u v=G k v u)
    (gl : ∀ k v, G k v v=false)
    (tf : ∀ k u v w, G k u v=true → G k u w=true → G k v w=false)
    (L : Kernel Y)
    (size : Tendsto (fun k => Fintype.card (V k)) atTop atTop)
    (ha : ∀ ε>0, ∀ᶠ k in atTop, ∃ π : Measure (V k×Y),
      MeasurePreserving Prod.fst π uniformVertices ∧ MeasurePreserving Prod.snd π ν ∧ π univ=1 ∧
      CutBound π (pullKernel (adjacencyKernel (G k) (sym k)) Prod.fst measurable_fst)
        (pullKernel L Prod.snd measurable_snd) ε)

private theorem normalized_edit_bound {V I : Type*} [Fintype V] [Fintype I]
    (G : V→V→Bool) (B : I→I→Bool) (q : V→I) (kp : 0<Fintype.card V)
    (he : ((directedErrors G B q).card : ℝ)/(Fintype.card V : ℝ)^2 ≤ (1/10000000 : ℝ)^2) :
    ((directedErrors G B q).card : ℝ) ≤ ((Fintype.card V : ℝ)/10000000)^2 := by
  have np : 0 < (Fintype.card V : ℝ) := by exact_mod_cast kp
  have h := (div_le_iff₀ (sq_pos_of_pos np)).mp he
  calc
    _ ≤ _ := h
    _ = _ := by ring

include gl tf size ha deq ord
theorem c5_binary_limit_stability (g : Y→Fin 5) (hg : Measurable g)
    (bin : L.W =ᵐ[ν.prod ν] (fun z => edgeReal (C5Stability.adj (g z.1) (g z.2))))
    (balanced : ∀ i, ν.real (cell g i)=1/5) :
    ∀ᶠ k in atTop, beta uniformVertices (adjacencyKernel (G k) (sym k))≤1/50 := by
  have H := binary_limit_has_edit_labeling ν G sym gl C5Stability.adj c5BaseAdj_sym
    c5BaseAdj_loopless L g hg bin size ha (1/10000000) (by norm_num)
  have pos : ∀ᶠ k in atTop, 0<Fintype.card (V k) := size.eventually (eventually_gt_atTop 0)
  filter_upwards [H,pos] with k ⟨q,hq,hd⟩ kp
  apply beta_le_of_finite_sparse (G k) (sym k) (gl k) kp
  apply c5_edit_stability (G k) q (sym k) (tf k) kp
    (normalized_edit_bound _ _ _ kp hd)
  intro i
  have np : 0 < (Fintype.card (V k) : ℝ) := by exact_mod_cast kp
  have h := (abs_le.mp (hq i)).1
  rw [balanced i] at h
  apply (le_div_iff₀ np).mp
  linarith

theorem petersen_binary_limit_stability (g : Y→Fin 10) (hg : Measurable g)
    (bin : L.W =ᵐ[ν.prod ν] (fun z => edgeReal (petersenBaseAdj (g z.1) (g z.2))))
    (balanced : ∀ i, ν.real (cell g i)=1/10) :
    ∀ᶠ k in atTop, beta uniformVertices (adjacencyKernel (G k) (sym k))≤1/50 := by
  have H := binary_limit_has_edit_labeling ν G sym gl petersenBaseAdj petersenBaseAdj_sym
    petersenBaseAdj_loopless L g hg bin size ha (1/10000000) (by norm_num)
  have pos : ∀ᶠ k in atTop, 0<Fintype.card (V k) := size.eventually (eventually_gt_atTop 0)
  filter_upwards [H,pos] with k ⟨q,hq,hd⟩ kp
  apply beta_le_of_finite_sparse (G k) (sym k) (gl k) kp
  apply petersen_edit_stability (G k) q (sym k) (tf k) kp
    (normalized_edit_bound _ _ _ kp hd)
  intro i
  have np : 0 < (Fintype.card (V k) : ℝ) := by exact_mod_cast kp
  have h := (abs_le.mp (hq i)).1
  rw [balanced i] at h
  apply (le_div_iff₀ np).mp
  linarith

theorem balanced_binary_limit_contradiction
    (hbad : ∀ᶠ k in atTop, 1/50<beta uniformVertices (adjacencyKernel (G k) (sym k)))
    (shape : (∃ g : Y→Fin 5, Measurable g ∧ (∀ i, ν.real (cell g i)=1/5) ∧
      L.W =ᵐ[ν.prod ν] (fun z => edgeReal (C5Stability.adj (g z.1) (g z.2)))) ∨
      (∃ g : Y→Fin 10, Measurable g ∧ (∀ i, ν.real (cell g i)=1/10) ∧
      L.W =ᵐ[ν.prod ν] (fun z => edgeReal (petersenBaseAdj (g z.1) (g z.2))))) :
    False := by
  have H : ∀ᶠ k in atTop, beta uniformVertices (adjacencyKernel (G k) (sym k))≤1/50 := by
    rcases shape with ⟨g,hg,bal,bin⟩ | ⟨g,hg,bal,bin⟩
    · exact c5_binary_limit_stability ν G sym gl tf L size ha g hg bin bal
    · exact petersen_binary_limit_stability ν G sym gl tf L size ha g hg bin bal
  obtain ⟨k,h1,h2⟩ := (hbad.and H).exists
  exact (not_lt_of_ge h2) h1

end

#print axioms c5_binary_limit_stability
#print axioms petersen_binary_limit_stability
#print axioms balanced_binary_limit_contradiction
end SparseHalfGraphon
