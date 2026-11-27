import FiniteGreedyReduction
import FiniteKernelNeighborhood
import GreedyShortfall
import SaturatedSampleLimit

open Set MeasureTheory Filter Topology Function
open scoped BigOperators
namespace SparseHalfGraphon

section
variable {V : Type*} [DecidableEq V]

def finiteMark (A : Finset V) (x : V) : Fin 2 := if x∈A then 0 else 1

lemma finiteMark_zero (A : Finset V) : cell (finiteMark A) (0:Fin 2) = (A:Set V) := by
  ext x
  change finiteMark A x = 0 ↔ x∈A
  by_cases h:x∈A <;> simp [finiteMark,h]
end

theorem finite_greedy_shortfall_limit {V : ℕ→Type*}
    [∀ k, Fintype (V k)] [∀ k, MeasurableSpace (V k)] [∀ k, MeasurableSingletonClass (V k)]
    [∀ k, DecidableEq (V k)]
    (G : ∀ k,V k→V k→Bool) (sym : ∀ k u v,G k u v=G k v u)
    (loop : ∀ k u,G k u u=false)
    (tf : ∀ k u v w,G k u v=true → G k u w=true → G k v w=false)
    (m : ℕ→ℕ) (hn : ∀ k,Fintype.card (V k)=2*m k) (hp : ∀ k,0<Fintype.card (V k))
    (A : ∀ k, Finset (V k)) (hInd : ∀ k,IndependentCells (G k) (A k:Set (V k)))
    (a : ℕ→ℝ) (ha : ∀ k,a k=((A k).card:ℝ)/(Fintype.card (V k):ℝ))
    (ha0 : ∀ k,39/100≤a k) (haLim : Tendsto a atTop (𝓝 (2/5)))
    (hcap : ∀ k (s : Finset (V k)),IndependentCells (G k) (s:Set (V k)) →
      (s.card:ℝ)/(Fintype.card (V k):ℝ)≤a k)
    (hBad : ∀ k,1/50<beta uniformVertices (adjacencyKernel (G k) (sym k))) :
    Tendsto (fun k=>∫ x,outsideShortfall (finiteMark (A k)) (0:Fin 2)
      (deg (uniformVertices.restrict (A k:Set (V k))) (adjacencyKernel (G k) (sym k))) (1/10) x
      ∂(uniformVertices : Measure (V k))) atTop (𝓝 0) := by
  let μ (k : ℕ) : Measure (V k) := uniformVertices
  let W (k : ℕ) := adjacencyKernel (G k) (sym k)
  have h (k) := finite_greedy_reduction (G k) (sym k) (loop k) (tf k) (m k) (hn k) (hp k)
    (A k) (hInd k) (a k) (ha k) (ha0 k) (hcap k) (hBad k)
  let B (k) := (h k).choose
  let b (k) := (μ k).real (B k:Set (V k))
  have hB (k) := (h k).choose_spec
  let F (k) := (a k*(1/2-a k)/2-1/50)/(3/100)
  have hF : Tendsto F atTop (𝓝 0) := by
    let P (a : ℝ) := (a*(1/2-a)/2-1/50)/(3/100)
    have hp : Continuous P := by unfold P; fun_prop
    have hz : P (2/5)=0 := by norm_num [P]
    simpa only [hz,Function.comp_def,F,P] using (hp.continuousAt.tendsto.comp haLim)
  have hg : Tendsto (fun k=>b k-a k) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hF
      (fun k=>sub_nonneg.mpr (hB k).2.2.1) (fun k=>?_ )
    have H := (hB k).2.2.2.2
    apply (le_div_iff₀ (by norm_num : 0<(3/100:ℝ))).mpr
    change 1/50+(3/100)*(b k-a k)<a k*(1/2-a k)/2 at H
    linarith
  have hb : Tendsto b atTop (𝓝 (2/5)) := by
    have H := haLim.add hg
    convert H using 1
    · funext k
      ring
    · norm_num
  have hq : Tendsto (fun k=>max 0 (b k-2/5)+(b k-a k)) atTop (𝓝 0) := by
    have H := ((tendsto_const_nhds (x:=(0:ℝ))).max (hb.sub (tendsto_const_nhds (x:=(2/5:ℝ))))).add hg
    convert H using 1 <;> norm_num
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hq (fun k=>?_) (fun k=>?_)
  · have H := outsideShortfall_unit (finiteMark (A k)) (measurable_of_countable _) (0:Fin 2)
      (deg ((μ k).restrict (A k:Set (V k))) (W k)) (deg_measurable _ _) (deg_nonneg _ _) (1/10) (by norm_num)
    exact integral_nonneg (fun x=>(H.2 x).1)
  · have ha' : (μ k).real (A k:Set (V k))=a k := (uniform_finset _).trans (ha k).symm
    have h1 := greedy_shortfall (μ k) (uniform_mass (hp k)) (W k) (finiteMark (A k))
      (measurable_of_countable _) (0:Fin 2) (B k:Set (V k)) (B k).finite_toSet.measurableSet
      (by rw [finiteMark_zero]; exact (hB k).1) (by
        rw [finiteMark_zero,ha']
        exact (hB k).2.1)
    rw [finiteMark_zero,ha'] at h1
    change _ ≤ max 0 (b k-2/5)+b k-a k at h1
    linarith

#print axioms finite_greedy_shortfall_limit
end SparseHalfGraphon
