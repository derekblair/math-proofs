import SaturatedLimit
import LowerMarkLimit
import HighMarkLimit

open Set MeasureTheory Filter Topology Function
namespace SparseHalfGraphon

/-- Near-endpoint input samples admitting a vanishing marked shortfall
have an obstructing marked limit with saturated outside degrees. This
does not assume cut-continuity of independence. -/
theorem saturated_sample_limit {X : ℕ → Type*} [∀ k, MeasurableSpace (X k)]
    (μ : ∀ k, Measure (X k)) [∀ k, IsFiniteMeasure (μ k)] (hμ : ∀ k, μ k univ=1)
    (W : ∀ k, Kernel (X k)) (c : ∀ k, X k→Fin 2) (hc : ∀ k, Measurable (c k)) (i : Fin 2)
    (α : ℕ→ℝ) (hα : Tendsto α atTop (𝓝 (2/5)))
    (hA : Tendsto (fun k=>(μ k).real (cell (c k) i)) atTop (𝓝 (2/5)))
    (hInd : ∀ k, energyPair (μ k) (W k) (markWeight (c k) i) (markWeight (c k) i)=0)
    (hBeta : ∀ k, 1/50≤beta (μ k) (W k))
    (hTri : ∀ k, t3 (μ k) (W k) (W k) (W k)=0)
    (hMax : ∀ k, ∀ᵐ x ∂μ k, deg (μ k) (W k) x≤α k)
    (hHigh : ∀ k, (μ k).real
      (highOutside (μ k) (W k) (cell (c k) i) ((μ k).real (cell (c k) i)/2))≤α k)
    (hShort : Tendsto (fun k => ∫ x, outsideShortfall (c k) i
      (deg ((μ k).restrict (cell (c k) i)) (W k)) (1/10) x ∂μ k) atTop (𝓝 0)) :
    ∃ q : ℕ→ℕ, StrictMono q ∧ ∃ L : Kernel UnitHalfOpen,
    ∃ d : UnitHalfOpen→Fin 2, Measurable d ∧ unitμ.real (cell d i)=2/5 ∧
      energyPair unitμ L (markWeight d i) (markWeight d i)=0 ∧
      1/50≤beta unitμ L ∧ t3 unitμ L L L=0 ∧
      (∀ᵐ y ∂unitμ, y∉cell d i → 1/5≤deg (unitμ.restrict (cell d i)) L y) ∧
      ∀ ε>0, ∀ᶠ k in atTop, ∃ π : Measure (X (q k)×UnitHalfOpen),
        MeasurePreserving Prod.fst π (μ (q k)) ∧ MeasurePreserving Prod.snd π unitμ ∧
        π univ=1 ∧ π.real (labelMismatch (c (q k)) d)≤ε ∧
        CutBound π (pullKernel (W (q k)) Prod.fst measurable_fst)
          (pullKernel L Prod.snd measurable_snd) ε := by
  obtain ⟨q,hq,L,d,hd,ha⟩ := marked_graphon_compactness μ hμ W (by decide : 0<2) c hc
  have halign ε (he : 0<ε) : ∀ᶠ k in atTop, ∃ π : Measure (X (q k)×UnitHalfOpen),
      MeasurePreserving Prod.fst π (μ (q k)) ∧ MeasurePreserving Prod.snd π unitμ ∧
      π univ=1 ∧ CutBound π (pullKernel (W (q k)) Prod.fst measurable_fst)
        (pullKernel L Prod.snd measurable_snd) ε :=
    (ha ε he).mono (fun _ ⟨π,hp,hr,hπ,_,hh⟩ => ⟨π,hp,hr,hπ,hh⟩)
  obtain ⟨hm,hi⟩ := cut_limit_mark_facts (fun k=>μ (q k)) unitμ
    (fun k=>W (q k)) L (fun k=>c (q k)) d (fun k=>hc (q k)) hd i (2/5)
    (hA.comp hq.tendsto_atTop) (fun k=>hInd (q k)) ha
  obtain ⟨hb,ht⟩ := aligned_sparse_limit (fun k=>μ (q k)) unitμ (fun k=>W (q k)) L
    (1/50) (fun k=>hBeta (q k)) (fun k=>hTri (q k)) halign
  have hTotal := cut_limit_degree_cap (fun k=>μ (q k)) unitμ unitμ_mass (fun k=>W (q k)) L
    (2/5) (fun k=>α (q k)) (hα.comp hq.tendsto_atTop) (fun k=>hMax (q k)) halign
  have hr := cut_limit_outside_floor (fun k=>μ (q k)) unitμ (fun k=>W (q k)) L
    (fun k=>c (q k)) d (fun k=>hc (q k)) hd i (1/10) (by norm_num)
    (hShort.comp hq.tendsto_atTop) ha
  have hH := highOutside_limit_cap (fun k=>μ (q k)) unitμ (fun k=>W (q k)) L
    (fun k=>c (q k)) d (fun k=>hc (q k)) hd i (fun k=>α (q k)) (2/5)
    (hα.comp hq.tendsto_atTop) (Eventually.of_forall (fun k=>hHigh (q k))) ha
  rw [hm,show (2/5:ℝ)/2=1/5 by norm_num] at hH
  have hS := saturated_limit unitμ unitμ_mass L (cell d i) (hd (measurableSet_singleton i)) hm hi
    ((zero_triangle_iff_ae unitμ L).mp ht) hb hr hTotal hH
  exact ⟨q,hq,L,d,hd,hm,hi,hb,ht,hS,ha⟩

#print axioms saturated_sample_limit
end SparseHalfGraphon
