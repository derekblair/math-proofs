import FiniteGreedyReduction

open Set MeasureTheory Function
namespace SparseHalfGraphon

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V] [DecidableEq V]

theorem finite_bad_alpha_lt_endpoint
    (G : V→V→Bool) (sym : ∀ u v,G u v=G v u) (loop : ∀ v,G v v=false)
    (tf : ∀ u v w,G u v=true → G u w=true → G v w=false)
    (m : ℕ) (hn : Fintype.card V=2*m) (hp : 0<Fintype.card V)
    (A : Finset V) (hInd : IndependentCells G (A:Set V))
    (a : ℝ) (ha : a=(A.card:ℝ)/(Fintype.card V:ℝ))
    (hcap : ∀ s : Finset V, IndependentCells G (s:Set V) →
      (s.card:ℝ)/(Fintype.card V:ℝ)≤a)
    (hBad : 1/50<beta uniformVertices (adjacencyKernel G sym)) : a<2/5 := by
  by_contra! h
  have ha0 : 39/100≤a := by linarith
  obtain ⟨B,hAB,hf,hb₁,hb₂,hcost⟩ := finite_greedy_reduction G sym loop tf m hn hp A hInd
    a ha ha0 hcap hBad
  have h₁ := mul_nonneg (show 0≤a-2/5 by linarith) (show 0≤a-1/10 by linarith)
  have h₂ : a*(1/2-a)/2 ≤ 1/50 := by nlinarith only [h₁]
  have hnonneg := mul_nonneg (by norm_num : 0≤(3:ℝ)/100) (sub_nonneg.mpr hb₁)
  linarith only [hcost,h₂,hnonneg]

#print axioms finite_bad_alpha_lt_endpoint
end SparseHalfGraphon
