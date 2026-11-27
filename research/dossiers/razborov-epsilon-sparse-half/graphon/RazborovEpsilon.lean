import CappedSampleBank
import FiniteKernelFloor

open Set MeasureTheory Function Filter Topology
open scoped BigOperators
namespace SparseHalfGraphon

open SparseHalfStability
set_option maxHeartbeats 1600000
set_option maxRecDepth 2000

/-- There is a positive neighborhood below 2/5 with no sparse-half
obstructions. This is the intermediate question in Razborov §5. -/
theorem razborov_epsilon_no_obstruction :
    ∃ ε : ℝ, 0<ε ∧ ∀ n (Q : Obstruction n), Q.alpha < 2/5-ε := by
  classical
  by_contra! h
  have h' (ε : ℝ) (he : 0<ε) : ∃ n : ℕ, ∃ Q : Obstruction n, 2/5-ε≤Q.alpha := by
    exact h ε he
  obtain ⟨n,G,sym,A,a,loop,tf,hn,hp,hgrow,hInd,ha,ha0,haLim,hcap,hBad⟩ :=
    obstruction_sequence h'
  let V := obstructionVertices n
  obtain ⟨q,hq,L,d,hd,hM,hI,hβ,hTri,hSat,hCouple⟩ :=
    finite_saturated_sequence G sym loop tf (fun k=>n k*(k+1)) hn hp A hInd a ha ha0 haLim hcap hBad
  have hc (k : ℕ) : Measurable (finiteMark (A (q k))) := measurable_of_countable _
  have hInd' (k : ℕ) : IndependentCells (G (q k)) (cell (finiteMark (A (q k))) 0) := by
    rw [finiteMark_zero]
    exact hInd (q k)
  obtain ⟨I,ic,inn,⟨B⟩⟩ :=
    capped_sample_bank (fun k=>G (q k)) (fun k=>sym (q k)) (fun k=>tf (q k))
      (fun k=>a (q k)) (haLim.comp hq.tendsto_atTop) (fun k=>hcap (q k))
      L (fun k=>finiteMark (A (q k))) d hc hd 0 hInd' hM hTri hSat hCouple
  letI : Countable I := ic
  letI : Nonempty I := inn
  have hIA : energyPair unitμ L (indicatorWeight (cell d 0)) (indicatorWeight (cell d 0))=0 := hI
  have unitReal : unitμ.real univ=1 := unitμ_mass
  have shape := B.classify unitReal (hd (measurableSet_singleton (0:Fin 2))) hM hIA hβ
  letI (k : ℕ) : LinearOrder (V (q k)) :=
    LinearOrder.lift' (Fintype.equivFin (V (q k))) (Fintype.equivFin _).injective
  have hSimpleCouple (ε : ℝ) (he : 0<ε) :
      ∀ᶠ k in atTop, ∃ π : Measure (V (q k)×UnitHalfOpen),
        MeasurePreserving Prod.fst π uniformVertices ∧ MeasurePreserving Prod.snd π unitμ ∧
        π univ=1 ∧
        CutBound π (pullKernel (adjacencyKernel (G (q k)) (sym (q k))) Prod.fst measurable_fst)
          (pullKernel L Prod.snd measurable_snd) ε :=
    (hCouple ε he).mono (fun _ ⟨π,h1,h2,h3,_,h4⟩=>⟨π,h1,h2,h3,h4⟩)
  exact balanced_binary_limit_contradiction unitμ (fun k=>G (q k)) (fun k=>sym (q k))
    (fun k=>loop (q k)) (fun k=>tf (q k)) L (hgrow.comp hq.tendsto_atTop) hSimpleCouple
    (Eventually.of_forall (fun k=>hBad (q k))) shape

/-- Razborov's epsilon question for ordinary floor halves of finite
triangle-free graphs. This does NOT assert the unrestricted Erdős conjecture. -/
theorem razborov_sparse_half_epsilon :
    ∃ ε : ℝ, 0<ε ∧
      ∀ n : ℕ, ∀ G : Fin n→Fin n→Bool,
        (∀ u v,G u v=G v u) →
        (∀ u,G u u=false) →
        (∀ u v w,G u v=true → G u w=true → G v w=false) →
        (∃ A : Finset (Fin n), IndependentCells G (A:Set (Fin n)) ∧
          2/5-ε≤(A.card:ℝ)/(n:ℝ)) →
        ∃ H : Finset (Fin n), H.card=n/2 ∧
          ((inducedEdges G H).card:ℝ) ≤ (n:ℝ)^2/50 := by
  classical
  obtain ⟨ε,hε,hnone⟩ := razborov_epsilon_no_obstruction
  refine ⟨ε,hε,?_⟩
  intro n G sym loop tf hA
  by_cases n0 : n=0
  · subst n
    exact ⟨∅,by decide,by norm_num [inducedEdges]⟩
  have hn : 0<n := Nat.pos_of_ne_zero n0
  have pos : 0<Fintype.card (Fin n) := by simpa using hn
  have hB : beta uniformVertices (adjacencyKernel G sym) ≤ 1/50 := by
    by_contra! hbad
    obtain ⟨A,hAi,hAm⟩ := hA
    let s := (Finset.univ : Finset (Finset (Fin n))).filter
      (fun x : Finset (Fin n) => IndependentCells G (x:Set (Fin n)))
    have ha : A∈s := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hAi⟩
    obtain ⟨T,hTs,hMax⟩ := Finset.exists_max_image s Finset.card ⟨A,ha⟩
    have hTm : IndependentCells G (T:Set (Fin n)) := (Finset.mem_filter.mp hTs).2
    let Q : Obstruction n := ⟨hn,G,sym,loop,tf,T,hTm,fun z hz=>
      hMax z (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩),hbad⟩
    have hh := hnone n Q
    have hm := div_le_div_of_nonneg_right (show (A.card:ℝ)≤(T.card:ℝ) by exact_mod_cast hMax A ha)
      (Nat.cast_nonneg n)
    change (T.card:ℝ)/(n:ℝ)<2/5-ε at hh
    linarith
  obtain ⟨H,hH,hcost⟩ := ordinary_floor_le_beta G sym loop pos
  have hpos : (0:ℝ)<n := by exact_mod_cast hn
  rw [Fintype.card_fin] at hH hcost
  refine ⟨H,hH,?_⟩
  have Hc := (div_le_iff₀ (sq_pos_of_pos hpos)).mp (hcost.trans hB)
  linarith

#print axioms razborov_epsilon_no_obstruction
#print axioms razborov_sparse_half_epsilon
end SparseHalfGraphon
