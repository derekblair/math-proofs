import GreedySequences

open Set MeasureTheory Filter Topology Function
open scoped BigOperators
namespace SparseHalfGraphon

/-- The finite near-endpoint reduction is fully integrated with compactness
and saturation. No analytic assumptions are imposed on the finite samples. -/
theorem finite_saturated_sequence {V : ℕ→Type*}
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
    ∃ q : ℕ→ℕ, StrictMono q ∧ ∃ L : Kernel UnitHalfOpen,
    ∃ d : UnitHalfOpen→Fin 2, Measurable d ∧ unitμ.real (cell d 0)=2/5 ∧
      energyPair unitμ L (markWeight d 0) (markWeight d 0)=0 ∧
      1/50≤beta unitμ L ∧ t3 unitμ L L L=0 ∧
      (∀ᵐ y ∂unitμ, y∉cell d 0 → 1/5≤deg (unitμ.restrict (cell d 0)) L y) ∧
      ∀ ε>0, ∀ᶠ k in atTop, ∃ π : Measure (V (q k)×UnitHalfOpen),
        MeasurePreserving Prod.fst π (uniformVertices : Measure (V (q k))) ∧
        MeasurePreserving Prod.snd π unitμ ∧
        π univ=1 ∧ π.real (labelMismatch (finiteMark (A (q k))) d)≤ε ∧
        CutBound π (pullKernel (adjacencyKernel (G (q k)) (sym (q k))) Prod.fst measurable_fst)
          (pullKernel L Prod.snd measurable_snd) ε := by
  let μ (k : ℕ) : Measure (V k) := uniformVertices
  let W (k : ℕ) := adjacencyKernel (G k) (sym k)
  let c (k : ℕ) := finiteMark (A k)
  apply saturated_sample_limit μ (fun k=>(uniform_probability (hp k)).measure_univ)
    W c (fun _=>measurable_of_countable _) 0 a haLim
  · have hM k : (μ k).real (cell (c k) 0)=a k := by
      change (μ k).real (cell (finiteMark (A k)) 0)=_
      rw [finiteMark_zero,uniform_finset,ha k]
    simpa only [hM] using haLim
  · intro k
    have hx : ∀ᵐ z ∂(μ k).prod (μ k), (markWeight (c k) 0 z.1*markWeight (c k) 0 z.2*(W k).W z)=0 := by
      apply ae_of_all
      intro z
      classical
      have he : cell (c k) 0=(A k:Set (V k)) := finiteMark_zero (A k)
      by_cases h₁ : z.1∈A k
      · by_cases h₂ : z.2∈A k
        · have hh : (W k).W z=0 := by
            change edgeReal (G k z.1 z.2)=0
            simp [edgeReal,hInd k z.1 h₁ z.2 h₂]
          simp [hh]
        · simp [markWeight,he,h₂]
      · simp [markWeight,he,h₁]
    unfold energyPair
    rw [integral_congr_ae hx]
    simp
  · exact fun k=>(hBad k).le
  · exact fun k=>(zero_triangle_iff_ae (μ k) (W k)).mpr (adjacency_triangle_ae (G k) (sym k) (tf k))
  · exact fun k=>ae_of_all _ (finite_degree_le_alpha (G k) (sym k) (tf k) (a k) (hcap k))
  · exact fun k=>finite_highOutside_cap (G k) (sym k) (tf k) (cell (c k) 0) (a k) (hcap k)
  · have hS := finite_greedy_shortfall_limit G sym loop tf m hn hp A hInd a ha ha0 haLim hcap hBad
    simpa only [c,finiteMark_zero] using hS

#print axioms finite_saturated_sequence
end SparseHalfGraphon
