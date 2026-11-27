import ActivePullCap
import HighMarkTransport

open MeasureTheory Set Function
open scoped BigOperators
namespace SparseHalfGraphon

variable {V Y I : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
  [MeasurableSpace Y] [MeasurableSpace I] [MeasurableSingletonClass I]
  (ν : Measure Y) [IsFiniteMeasure ν] (π : Measure (V×Y)) [IsFiniteMeasure π]

theorem active_cap_aligned (hp : MeasurePreserving Prod.fst π uniformVertices)
    (hq : MeasurePreserving Prod.snd π ν)
    (G : V→V→Bool) (sym : ∀ u v, G u v=G v u)
    (tf : ∀ u v w, G u v=true → G u w=true → G v w=false)
    (α : ℝ) (cap : ∀ s : Finset V, IndependentCells G (s : Set V) →
      (s.card : ℝ)/(Fintype.card V : ℝ) ≤ α)
    (L : Kernel Y) (c : V→I) (d : Y→I) (hc : Measurable c) (hd : Measurable d) (i : I)
    (ind : IndependentCells G (cell c i))
    (S Q P T : Set Y) (sM : MeasurableSet S) (qM : MeasurableSet Q)
    (pM : MeasurableSet P) (tM : MeasurableSet T)
    (pOutside : P ⊆ (cell d i)ᶜ) (tInside : T ⊆ cell d i)
    (sPos : 0 < ν.real S) (τ : ℝ) (tPos : 0 < τ)
    (pS : ∀ y ∈ P, deg (ν.restrict S) L y = ν.real S)
    (pQ : ∀ y ∈ P, 2*τ < deg (ν.restrict Q) L y)
    (tQ : ∀ y ∈ T, deg (ν.restrict Q) L y = ν.real Q)
    (ε : ℝ)
    (cut : CutBound π (pullKernel (adjacencyKernel G sym) Prod.fst measurable_fst)
      (pullKernel L Prod.snd measurable_snd) ε) :
    ν.real P+ν.real T ≤ α + 2*π.real (labelMismatch c d) +
      (2*ε)/(ν.real S/2) + 2*((2*ε)/τ) := by
  let K := pullKernel (adjacencyKernel G sym) Prod.fst hp.measurable
  let A : Set (V×Y) := Prod.fst ⁻¹' cell c i
  let SQ : Set (V×Y) := Prod.snd ⁻¹' S
  let QQ : Set (V×Y) := Prod.snd ⁻¹' Q
  have mA : MeasurableSet A := hp.measurable (hc (measurableSet_singleton i))
  have mS : MeasurableSet SQ := hq.measurable sM
  have mQ : MeasurableSet QQ := hq.measurable qM
  have mSM : π.real SQ = ν.real S := real_mass_pull hq sM
  have mQM : π.real QQ = ν.real Q := real_mass_pull hq qM
  let a := deg (π.restrict SQ) K
  let b := deg (π.restrict QQ) K
  let err (R : Set Y) (z : V×Y) :=
    |deg (π.restrict (Prod.snd ⁻¹' R)) K z - deg (ν.restrict R) L z.2|
  let ES := {z | ν.real S/2 ≤ err S z}
  let EQ := {z | τ ≤ err Q z}
  let mismatch := labelMismatch c d
  have tails (R : Set Y) (mR : MeasurableSet R) (u : ℝ) (uPos : 0<u) :
      π.real {z | u≤err R z} ≤ (2*ε)/u := by
    let f := deg (π.restrict (Prod.snd ⁻¹' R)) K
    let g : V×Y → ℝ := deg (ν.restrict R) L ∘ Prod.snd
    have ef : Integrable f π :=
      integrable_bounded π (deg_measurable _ K) (deg_nonneg _ K) (deg_le_mass _ K)
    have eg : Integrable g π :=
      integrable_bounded π ((deg_measurable _ L).comp hq.measurable)
        (fun z => deg_nonneg (ν.restrict R) L z.2)
        (fun z => deg_le_mass (ν.restrict R) L z.2)
    have em : Measurable (err R) :=
      continuous_abs.measurable.comp ((deg_measurable _ K).sub ((deg_measurable _ L).comp hq.measurable))
    refine (tail_mass_integral π (err R) em (ef.sub eg).abs (fun _ => abs_nonneg _) u uPos).trans
      (div_le_div_of_nonneg_right ?_ uPos.le)
    have hh := cut_degree_L1 π K (pullKernel L Prod.snd measurable_snd) ε cut
      (Prod.snd ⁻¹' R) (hq.measurable mR)
    convert hh using 1
    congr 1
    funext z
    rw [degree_pull_restricted hq mR L z]
  have ts : π.real ES ≤ (2*ε)/(ν.real S/2) := tails S sM _ (by positivity)
  have tq : π.real EQ ≤ (2*ε)/τ := tails Q qM _ tPos
  let U := (Prod.snd ⁻¹' P) ∩ Aᶜ ∩ {x | π.real SQ/2 < a x} ∩ {x | τ < b x}
  let T' := (Prod.snd ⁻¹' T) ∩ A ∩ {x | π.real QQ-τ < b x}
  have hT' : MeasurableSet T' :=
    ((hq.measurable tM).inter mA).inter (measurableSet_lt measurable_const (deg_measurable _ K))
  have dis : Disjoint U T' := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact hz.1.1.2 hz'.1.2
  have H : π.real U+π.real T' ≤ α := by
    apply active_pull_cap π Prod.fst hp G sym tf α cap SQ QQ U T' mS mQ hT' dis
      (fun x hx y hy => ind _ hx.1.2 _ hy.1.2) τ
    · exact fun x hx => hx.1.2
    · exact fun x hx => hx.2
    · exact fun x hx => hx.2
  have pSub : Prod.snd ⁻¹' P ⊆ ((U ∪ mismatch) ∪ ES) ∪ EQ := by
    intro z hz
    by_cases hQ : z ∈ EQ
    · exact Or.inr hQ
    refine Or.inl ?_
    by_cases hS : z ∈ ES
    · exact Or.inr hS
    refine Or.inl ?_
    by_cases hm : z ∈ mismatch
    · exact Or.inr hm
    refine Or.inl ⟨⟨⟨hz,?_⟩,?_⟩,?_⟩
    · intro hzA
      have eq : c z.1=d z.2 := by
        by_contra h
        exact hm h
      exact pOutside hz (eq.symm.trans hzA)
    · rw [mSM]
      have e₁ : err S z < ν.real S/2 := lt_of_not_ge hS
      have e₂ : deg (ν.restrict S) L z.2 - a z ≤ err S z := by
        simpa only [err,a,neg_sub] using neg_le_abs (a z - deg (ν.restrict S) L z.2)
      change ν.real S/2 < a z
      linarith [pS z.2 hz]
    · have e₁ : err Q z < τ := lt_of_not_ge hQ
      have e₂ : deg (ν.restrict Q) L z.2 - b z ≤ err Q z := by
        simpa only [err,b,neg_sub] using neg_le_abs (b z - deg (ν.restrict Q) L z.2)
      change τ < b z
      linarith [pQ z.2 hz]
  have tSub : Prod.snd ⁻¹' T ⊆ (T' ∪ mismatch) ∪ EQ := by
    intro z hz
    by_cases hQ : z ∈ EQ
    · exact Or.inr hQ
    refine Or.inl ?_
    by_cases hm : z ∈ mismatch
    · exact Or.inr hm
    refine Or.inl ⟨⟨hz,?_⟩,?_⟩
    · have eq : c z.1=d z.2 := by
        by_contra h
        exact hm h
      exact eq.trans (tInside hz)
    · rw [mQM]
      have e₁ : err Q z < τ := lt_of_not_ge hQ
      have e₂ : deg (ν.restrict Q) L z.2 - b z ≤ err Q z := by
        simpa only [err,b,neg_sub] using neg_le_abs (b z - deg (ν.restrict Q) L z.2)
      change ν.real Q-τ < b z
      linarith [tQ z.2 hz]
  have Pbound : ν.real P ≤ π.real U+π.real mismatch+π.real ES+π.real EQ := by
    rw [← real_mass_pull hq pM]
    have h := (measureReal_mono (μ:=π) pSub).trans (measureReal_union_le _ _)
    linarith [measureReal_union_le (μ:=π) (U ∪ mismatch) ES,measureReal_union_le (μ:=π) U mismatch]
  have Tbound : ν.real T ≤ π.real T'+π.real mismatch+π.real EQ := by
    rw [← real_mass_pull hq tM]
    have h := (measureReal_mono (μ:=π) tSub).trans (measureReal_union_le _ _)
    linarith [measureReal_union_le (μ:=π) T' mismatch]
  linarith only [Pbound,Tbound,H,ts,tq]

#print axioms active_cap_aligned
end SparseHalfGraphon
