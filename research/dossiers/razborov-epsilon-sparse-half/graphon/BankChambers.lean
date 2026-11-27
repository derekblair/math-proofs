import BankPools
import TwoHeavyKernel
import StrictDominantSaturated
import FinalTemplateStability

open Set MeasureTheory Function Filter
open scoped ENNReal BigOperators
namespace SparseHalfGraphon
set_option maxHeartbeats 1600000
set_option maxRecDepth 1600

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [IsFiniteMeasure μ]
variable {K : Kernel Y} {A : Set Y} {I : Type*} (B : ActiveBank μ K A I)

lemma finset_embedding (s : Finset I) {n : ℕ} (hn : s.card=n) :
    ∃ e : Fin n ↪ I, ∀ i, e i∈s := by
  classical
  let e : {x : I // x ∈ s} ≃ Fin n := Fintype.equivFinOfCardEq ((Fintype.card_coe s).trans hn)
  exact ⟨⟨fun i=>(e.symm i).val,fun _ _ h=>e.symm.injective (Subtype.ext h)⟩,fun i=>(e.symm i).property⟩

def pairEmbedding (i j : I) (h : i≠j) : Fin 2 ↪ I :=
  ⟨![i,j],by intro a b he; fin_cases a <;> fin_cases b <;> simp_all⟩

lemma scale_anchor_four (hm : μ.real A=2/5) :
    ((10:ℝ≥0∞) • μ.restrict A).real univ=4 := by
  rw [measureReal_ennreal_smul_apply,measureReal_restrict_apply_univ,hm]
  norm_num

lemma ActiveBank.pick_embedding_disj {n : ℕ} (e : Fin n ↪ I) :
    Pairwise (fun u v : Fin n×Bool => Disjoint (B.pick (e u.1) u.2) (B.pick (e v.1) v.2)) := by
  intro u v ne
  apply B.pick_disj (e u.1,u.2) (e v.1,v.2)
  intro h
  exact ne (Prod.ext (e.injective (congrArg Prod.fst h)) (congrArg (fun z : I×Bool=>z.2) h))

/-- Unit outside pairs give exactly the Petersen branch for a tight kernel. -/
theorem ActiveBank.petersen_of_unit (hA : MeasurableSet A) (hAm : μ.real A=2/5)
    (hμ : μ.real univ=1)
    (hZ : ∀ᵐ z ∂(μ.restrict A).prod (μ.restrict A), K.W z=0)
    (hb : 1/50≤beta μ K) (s : Finset I) (h3 : s.card=3)
    (hs : ∀ j∈s, B.p j=1 ∧ B.q j=1) :
    ∃ g : Y→Fin 10, Measurable g ∧ (∀ i,μ.real (cell g i)=1/10) ∧
      K.W =ᵐ[μ.prod μ] (fun z=>edgeReal (petersenBaseAdj (g z.1) (g z.2))) := by
  obtain ⟨e,he⟩ := finset_embedding s h3
  let P (i : Fin 3) (b : Bool) := B.pick (e i) b
  let S (i : Fin 3) := B.pickSig (e i)
  have hp i : 0<B.p (e i) := by rw [(hs _ (he i)).1]; norm_num
  obtain ⟨H,hH⟩ | ⟨g,hg,hbal,hbin⟩ :=
    SparseHalfCountableEndpoint.three_unit_completed_kernel μ K A hA P S
      (fun i b=>B.pick_meas _ _) (fun i=>B.pickSig_meas _)
      (B.pick_embedding_disj e) (fun i b=>B.pick_out _ _) (fun i b=>by
        change μ.real (B.pick (e i) b)=_
        rw [B.pick_mass,(hs _ (he i)).1,(hs _ (he i)).2]
        cases b <;> rfl)
      hZ (fun i j b c h=>B.pick_zero _ _ _ _ (fun x=>h (e.injective x)))
      (fun i b=>B.pick_cross _ _) (scale_anchor_four hAm)
      (fun i=>B.pickSig_mass _ (hp i) hAm) hμ
  · exact False.elim ((not_lt_of_ge (hb.trans (csInf_le (range_bdd μ K) ⟨H,rfl⟩))) hH)
  · exact SparseHalfCountableEndpoint.petersen_label_for_transfer μ K g hg hbal hbin

theorem ActiveBank.two_large_light_bad (hA : MeasurableSet A) (hAm : μ.real A=2/5)
    (hZ : ∀ᵐ z ∂(μ.restrict A).prod (μ.restrict A), K.W z=0)
    (hb : 1/50≤beta μ K) (s : Finset I) (h2 : s.card=2)
    (hs : ∀ j∈s, B.p j=2 ∧ B.q j=1) : False := by
  obtain ⟨e,he⟩ := finset_embedding s h2
  let P (i : Fin 2) (b : Bool) := B.pick (e i) b
  let S (i : Fin 2) := B.pickSig (e i)
  have hp i : 0<B.p (e i) := by rw [(hs _ (he i)).1]; norm_num
  obtain ⟨H, hH⟩ :=
    SparseHalfCountableEndpoint.two_large_light_strict μ K A hA P S
      (fun i b=>B.pick_meas _ _) (fun i=>B.pickSig_meas _)
      (fun i j b c ne=>B.pick_embedding_disj e (show (i,b)≠(j,c) from
        fun h=>ne (congrArg Prod.fst h))) (fun i b=>B.pick_out _ _) (fun i b=>by
        change μ.real (B.pick (e i) b)=_
        rw [B.pick_mass,(hs _ (he i)).1,(hs _ (he i)).2]
        cases b <;> norm_num)
      hZ (fun i j b c h=>B.pick_zero _ _ _ _ (fun x=>h (e.injective x)))
      (fun i b=>B.pick_cross _ _) (scale_anchor_four hAm)
      (fun i=>B.pickSig_mass _ (hp i) hAm)
  exact (not_lt_of_ge (hb.trans (csInf_le (range_bdd μ K) ⟨H,rfl⟩))) hH

theorem ActiveBank.two_heavy_bad (hA : MeasurableSet A) (hAm : μ.real A=2/5)
    (hZ : ∀ᵐ z ∂(μ.restrict A).prod (μ.restrict A), K.W z=0)
    (hb : 1/50≤beta μ K) (i j : I) (hij : i≠j)
    (hi : 1<B.q i) (hj : 1<B.q j) (hh : B.p i≤B.p j)
    (L : ℝ) (hL : B.h+L≤2)
    (hs : B.p j*(4-max (B.p i+B.q j) (B.p j+B.q i))<2 ∨
      (B.h=2/3 ∧ B.p i=3/2 ∧ B.p j=3/2 ∧ B.q i=7/6 ∧ B.q j=7/6 ∧ L=0)) :
    False := by
  let e := pairEmbedding i j hij
  let P (i : Fin 2) (b : Bool) := B.pick (e i) b
  let S (i : Fin 2) := B.pickSig (e i)
  have hpi : 0<B.p i := by linarith [B.q_le_p i]
  have hpj : 0<B.p j := by linarith [B.q_le_p j]
  have hp t : 0<B.p (e t) := by
    fin_cases t
    · exact hpi
    · exact hpj
  obtain ⟨H, hH⟩ :=
    SparseHalfCountableEndpoint.two_heavy_kernel_of_scalar μ K A hA P S
      (fun i b=>B.pick_meas _ _) (fun i=>B.pickSig_meas _)
      (fun i j b c ne=>B.pick_embedding_disj e (show (i,b)≠(j,c) from
        fun h=>ne (congrArg Prod.fst h))) (fun i b=>B.pick_out _ _)
      hZ (fun i j b c h=>B.pick_zero _ _ _ _ (fun x=>h (e.injective x)))
      (fun i b=>B.pick_cross _ _) (scale_anchor_four hAm)
      (fun i=>B.pickSig_mass _ (hp i) hAm)
      B.h (B.p i) (B.q i) (B.p j) (B.q j) L (fun t b=>by
        change μ.real (B.pick (e t) b)=_
        rw [B.pick_mass]
        fin_cases t <;> rfl)
      hi hj (B.q_le_p i) (B.q_le_p j) hh (B.p_upper j) hL hs
  exact (not_lt_of_ge (hb.trans (csInf_le (range_bdd μ K) ⟨H,rfl⟩))) hH

#print axioms ActiveBank.petersen_of_unit
#print axioms ActiveBank.two_large_light_bad
#print axioms ActiveBank.two_heavy_bad
end SparseHalfGraphon
