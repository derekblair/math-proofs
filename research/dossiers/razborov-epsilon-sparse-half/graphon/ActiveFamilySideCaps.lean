import ActiveCapLimit
import ActivePairLocal

open MeasureTheory Set Function Filter Topology
open scoped ENNReal
namespace SparseHalfGraphon

theorem active_family_side_caps {V : ℕ→Type*}
    [∀ k, Fintype (V k)] [∀ k, MeasurableSpace (V k)] [∀ k, MeasurableSingletonClass (V k)]
    {Y : Type*} [MeasurableSpace Y]
    {I : Type*}
    (μ : Measure Y) [IsFiniteMeasure μ]
    (G : ∀ k, V k→V k→Bool) (sym : ∀ k u v, G k u v=G k v u)
    (tf : ∀ k u v w, G k u v=true → G k u w=true → G k v w=false)
    (αs : ℕ→ℝ) (hα : Tendsto αs atTop (𝓝 (2/5)))
    (cap : ∀ k (s : Finset (V k)), IndependentCells (G k) (s : Set (V k)) →
      (s.card : ℝ)/(Fintype.card (V k) : ℝ) ≤ αs k)
    (L : Kernel Y) (c : ∀ k, V k→Fin 2) (d : Y→Fin 2) (hc : ∀ k, Measurable (c k))
    (hd : Measurable d) (i : Fin 2) (ind : ∀ k, IndependentCells (G k) (cell (c k) i))
    (ha : ∀ ε > 0, ∀ᶠ k in atTop, ∃ π : Measure (V k×Y),
      MeasurePreserving Prod.fst π uniformVertices ∧ MeasurePreserving Prod.snd π μ ∧
      π univ=1 ∧ π.real (labelMismatch (c k) d)≤ε ∧
      CutBound π (pullKernel (adjacencyKernel (G k) (sym k)) Prod.fst measurable_fst)
        (pullKernel L Prod.snd measurable_snd) ε)
    (hA : μ.real (cell d i)=2/5)
    (P Q R : I→Set Y)
    (meas : ∀ j, MeasurableSet (P j) ∧ MeasurableSet (Q j) ∧ MeasurableSet (R j))
    (inside : ∀ j, P j∪Q j ⊆ (cell d i)ᶜ)
    (inner : ∀ j, Disjoint (P j) (Q j))
    (outer : Pairwise (Disjoint on fun j => P j∪Q j))
    (edge : ∀ᵐ z ∂(μ.restrict (cell d i)ᶜ).prod (μ.restrict (cell d i)ᶜ), 0<L.W z → ∃ j,
      (z.1∈P j ∧ z.2∈Q j) ∨ (z.1∈Q j ∧ z.2∈P j))
    (active : ∀ᵐ x ∂μ.restrict (cell d i)ᶜ,
      x∈(⋃ j,P j∪Q j) ↔ 0<deg (μ.restrict (cell d i)ᶜ) L x)
    (profiles : ∀ j, (P j=∅ ∧ Q j=∅) ∨
      (0<(μ.restrict (cell d i)ᶜ).real (P j) ∧ 0<(μ.restrict (cell d i)ᶜ).real (Q j) ∧
      (μ.restrict (cell d i)).real (R j)=mass (μ.restrict (cell d i))/2 ∧
      (μ.restrict (cell d i)).real (R j)ᶜ=mass (μ.restrict (cell d i))/2 ∧
      (∀ᵐ v ∂μ.restrict (cell d i), (fun x=>L.W (v,x)) =ᵐ[(μ.restrict (cell d i)ᶜ).restrict (P j)]
        (fun _=>oneOn (R j) v)) ∧
      (∀ᵐ v ∂μ.restrict (cell d i), (fun x=>L.W (v,x)) =ᵐ[(μ.restrict (cell d i)ᶜ).restrict (Q j)]
        (fun _=>oneOn (R j)ᶜ v)) ∧
      (∀ᵐ x ∂(μ.restrict (cell d i)ᶜ).restrict (P j), (fun v=>L.W (x,v)) =ᵐ[μ.restrict (cell d i)]
        oneOn (R j)) ∧
      (∀ᵐ x ∂(μ.restrict (cell d i)ᶜ).restrict (Q j), (fun v=>L.W (x,v)) =ᵐ[μ.restrict (cell d i)]
        oneOn (R j)ᶜ)))
    (j : I) : μ.real (P j) ≤ 1/5 ∧ μ.real (Q j) ≤ 1/5 := by
  let A := cell d i
  let ω := μ.restrict Aᶜ
  let ν := μ.restrict A
  have mA : MeasurableSet A := hd (measurableSet_singleton i)
  have mP (k : I) := (meas k).1
  have mQ (k : I) := (meas k).2.1
  have ps (k : I) : P k ⊆ Aᶜ := fun x hx => inside k (Or.inl hx)
  have qs (k : I) : Q k ⊆ Aᶜ := fun x hx => inside k (Or.inr hx)
  have rp : ω.restrict (P j)=μ.restrict (P j) := Measure.restrict_restrict_of_subset (ps j)
  have rq : ω.restrict (Q j)=μ.restrict (Q j) := Measure.restrict_restrict_of_subset (qs j)
  rcases profiles j with ⟨hp,hq⟩ | ⟨_,_,mS,mT,bp,bq,fp,fq⟩
  · simp [hp,hq]
  have hM : mass ν=2/5 := by
    change (μ.restrict A).real univ=2/5
    rw [measureReal_restrict_apply_univ]
    exact hA
  have pairRows := paired_positive_row_confined ω L P Q mP mQ inner outer edge j
  have pActive : ∀ᵐ x ∂μ, x∈P j → 0 < deg (μ.restrict (Q j)) L x := by
    rw [← ae_restrict_iff' (mP j),← rp,← rq]
    have z := deg_restrict_of_row_confined ω L (P j) (Q j) (mQ j) pairRows.1
    filter_upwards [z,active.filter_mono (Measure.restrict_le_self (s := P j)).absolutelyContinuous.ae_le,
      ae_restrict_mem (μ := ω) (mP j)] with x hx ha hxP
    rw [hx]
    exact ha.mp (mem_iUnion.mpr ⟨j,Or.inl hxP⟩)
  have qActive : ∀ᵐ x ∂μ, x∈Q j → 0 < deg (μ.restrict (P j)) L x := by
    rw [← ae_restrict_iff' (mQ j),← rq,← rp]
    have z := deg_restrict_of_row_confined ω L (Q j) (P j) (mP j) pairRows.2
    filter_upwards [z,active.filter_mono (Measure.restrict_le_self (s := Q j)).absolutelyContinuous.ae_le,
      ae_restrict_mem (μ := ω) (mQ j)] with x hx ha hxQ
    rw [hx]
    exact ha.mp (mem_iUnion.mpr ⟨j,Or.inr hxQ⟩)
  have side (U W B : Set Y) (mU : MeasurableSet U) (mW : MeasurableSet W)
      (mB : MeasurableSet B) (uOut : U ⊆ Aᶜ)
      (massB : ν.real B=mass ν/2) (massC : ν.real Bᶜ=mass ν/2)
      (outRow : ∀ᵐ x ∂μ.restrict U, (fun v=>L.W (x,v)) =ᵐ[ν] oneOn B)
      (inRow : ∀ᵐ v ∂ν, (fun x=>L.W (v,x)) =ᵐ[μ.restrict W] (fun _=>oneOn Bᶜ v))
      (pos : ∀ᵐ x ∂μ, x∈U → 0 < deg (μ.restrict W) L x) :
      μ.real U ≤ 1/5 := by
    let S := A ∩ B
    let T := A ∩ Bᶜ
    have ms : MeasurableSet S := mA.inter mB
    have mt : MeasurableSet T := mA.inter mB.compl
    have sm : μ.real S=1/5 := by
      change (μ.restrict A).real B=mass ν/2 at massB
      rw [measureReal_restrict_apply mB,inter_comm,hM] at massB
      linarith
    have tm : μ.real T=1/5 := by
      change (μ.restrict A).real Bᶜ=mass ν/2 at massC
      rw [measureReal_restrict_apply mB.compl,inter_comm,hM] at massC
      linarith
    have mpS : ∀ᵐ x ∂μ, x∈U → deg (μ.restrict S) L x=μ.real S := by
      rw [← ae_restrict_iff' mU]
      filter_upwards [outRow] with x hx
      have hs : μ.restrict S ≤ ν := Measure.restrict_mono Set.inter_subset_left le_rfl
      have hh : (fun v=>L.W (x,v)) =ᵐ[μ.restrict S] (fun _=> (1:ℝ)) := by
        filter_upwards [hx.filter_mono hs.absolutelyContinuous.ae_le,ae_restrict_mem (μ:=μ) ms]
          with y hy hys
        simpa [oneOn,indicator_of_mem hys.2] using hy
      unfold deg
      rw [integral_congr_ae hh,integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ]
    have mtQ : ∀ᵐ x ∂μ, x∈T → deg (μ.restrict W) L x=μ.real W := by
      rw [← ae_restrict_iff' mt]
      have hs : μ.restrict T ≤ ν := Measure.restrict_mono Set.inter_subset_left le_rfl
      filter_upwards [inRow.filter_mono hs.absolutelyContinuous.ae_le,ae_restrict_mem (μ:=μ) mt]
        with x hx hxt
      have hh : (fun v=>L.W (x,v)) =ᵐ[μ.restrict W] (fun _=> (1:ℝ)) := by
        filter_upwards [hx] with y hy
        simpa [oneOn,indicator_of_mem hxt.2] using hy
      unfold deg
      rw [integral_congr_ae hh,integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ]
    have e := active_side_limit_cap μ G sym tf αs (2/5) hα cap L c d hc hd i ind
      S W U T ms mW mU mt uOut Set.inter_subset_left (by rw [sm]; norm_num) mpS pos mtQ ha
    linarith
  rw [rp] at bp fp
  rw [rq] at bq fq
  refine ⟨side (P j) (Q j) (R j) (mP j) (mQ j) (meas j).2.2 (ps j)
    mS mT fp bq pActive,?_⟩
  refine side (Q j) (P j) ((R j)ᶜ) (mQ j) (mP j) (meas j).2.2.compl (qs j)
    mT (by simpa using mS) fq ?_ qActive
  simpa using bp

#print axioms active_family_side_caps
end SparseHalfGraphon
