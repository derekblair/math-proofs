import AllocationLoads

open Set MeasureTheory Function Filter
open scoped ENNReal
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- A balanced allocation outside the low vertices, together with all
low vertices, is excluded by the strict Case 2 calculation. -/
theorem small_low_balanced_impossible (W : Kernel X) (a : X→ℝ)
    (ha : Measurable a) (ha₀ : ∀ x, 0 ≤ a x) (ha₁ : ∀ x, a x ≤ 1)
    (haM : (∫ x,a x ∂μ)=2/5) (haI : energyPair μ W a a=0)
    (htri : ∀ᵐ z ∂(μ.prod μ).prod μ, triangle W z=0)
    (hb : 1/50 ≤ beta μ W)
    (S L : Set X) (hS : MeasurableSet S) (hL : MeasurableSet L) (hLS : L ⊆ S)
    (hsa : ∀ x∈S, a x=0)
    (hsd : ∀ x∈S, 1/10≤deg (reweight μ a) W x ∧ deg (reweight μ a) W x≤1/5)
    (hld : ∀ x∈L, deg (reweight μ a) W x < 1/5)
    (hLM : 0 < μ.real L)
    (f : X→ℝ) (bF : BMeas f) (f0 : ∀ x, 0≤f x) (f1 : ∀ x, f x≤1)
    (fZ : ∀ x∉S\L, f x=0)
    (fMass : (∫ x,f x ∂μ)=1/5-μ.real L)
    (hf : ∀ᵐ v ∂reweight μ a, load μ W f v≤1/10) :
    False := by
  let q : ℝ := μ.real L
  have hq : q≤μ.real L := le_rfl
  have hqp : 0<q := hLM
  let e := allocSet μ L q
  let D := e+f
  have bE : BMeas e := allocSet_bmeas μ L hL q hqp.le hq
  have bD : BMeas D := bE.add bF
  have e0 x : 0≤e x := allocSet_nn μ L q hqp.le x
  have D0 x : 0≤D x := add_nonneg (e0 x) (f0 x)
  have eZ (x) (hx : x∉L) : e x=0 := allocSet_support μ L q hx
  have dZ (x) (hx : x∉S) : D x=0 := by
    change e x+f x=0
    rw [eZ x (fun h=>hx (hLS h)), fZ x (fun h=>hx h.1), add_zero]
  have dcap x : a x+D x≤1 := by
    classical
    by_cases hx : x∈S
    · rw [hsa x hx,zero_add]
      change e x+f x≤1
      by_cases hl : x∈L
      · rw [fZ x (fun h=>h.2 hl),add_zero]
        exact allocSet_le μ L q hq x
      · rw [eZ x hl,zero_add]
        exact f1 x
    · rw [dZ x hx,add_zero]
      exact ha₁ x
  have d1 x : D x≤1 := by linarith [dcap x,ha₀ x]
  have hDM : (∫ x,D x ∂μ)=1/5 := by
    change (∫ x,(e+f) x ∂μ)=1/5
    rw [integral_add' (bMeas_integrable μ bE) (bMeas_integrable μ bF),
      allocSet_mass μ L hL q hqp.le hq, fMass]
    dsimp [q]
    ring
  have ddeg (x) (hx : 0<D x) :=
    hsd x (by by_contra! h; rw [dZ x h] at hx; exact (lt_irrefl 0 hx))
  have hload : ∀ᵐ v ∂reweight μ a, load μ W D v ≤ 1/10 := by
    have hroot := (root_eligible_lt μ W a ha ha₀ ha₁ haM haI htri hb
      S L hS hL hLS hsa (fun x h =>(hsd x h).2) hld).filter_mono (reweight_ac μ a).ae_le
    filter_upwards [hroot,hf] with v hv hfv
    by_cases hp : 0 < μ (rowSupport W v L)
    · exact (load_le_mass_of_support μ W v S hS D bD D0 d1 dZ).trans (hv hp).le
    · have hnull : μ (rowSupport W v L)=0 := le_antisymm (not_lt.mp hp) bot_le
      have hE := load_le_mass_of_support μ W v L hL e bE e0 (allocSet_le μ L q hq) eZ
      change load μ W e v≤(μ (rowSupport W v L)).toReal at hE
      rw [hnull,ENNReal.toReal_zero] at hE
      change load μ W (e+f) v≤_
      rw [load_add μ W e f bE bF]
      exact (add_le_add hE hfv).trans_eq (zero_add _)
  have : IsFiniteMeasure (reweight μ a) := isFiniteMeasure_of_le μ (reweight_le μ a ha₁)
  have hZ : 0<defMass μ (reweight μ a) W D := by
    unfold defMass
    let g : X→ℝ := fun x=>D x*deficit (reweight μ a) W x
    have gi : Integrable g μ := bMeas_integrable μ
      (bD.mul ((BMeas.const _).sub (deg_bmeas (reweight μ a) W)))
    have g0 : 0≤g := by
      intro x
      classical
      by_cases hx : x∈S
      · exact mul_nonneg (D0 x) (sub_nonneg.mpr (hsd x hx).2)
      · simp [g,dZ x hx]
    have hSub : L ⊆ support g := by
      intro x hx
      apply ne_of_gt
      have he : 0<e x := allocSet_pos μ L q hqp hq hx
      have hd : 0 < D x := by change 0<e x+f x; linarith [f0 x]
      exact mul_pos hd (sub_pos.mpr (hld x hx))
    have hlpos : 0<μ L := by
      apply pos_iff_ne_zero.mpr
      intro hz
      have hz' : μ.real L=0 := by simp [Measure.real,hz]
      exact (ne_of_gt hLM) hz'
    exact (integral_pos_iff_support_of_nonneg g0 gi).mpr (hlpos.trans_le (measure_mono hSub))
  exact not_lt_of_ge hb (graphon_case_two μ W a D ha bD.1 ha₀ D0 dcap haM hDM haI htri ddeg hload hZ)

#print axioms small_low_balanced_impossible
end SparseHalfGraphon
