import GeometricSparseBernoulliTail

namespace RobustFolkman.GeometricGap
open MeasureTheory Set Finset
open scoped ENNReal
variable {S Ω I : Type*} [MeasurableSpace S] [MeasurableSpace Ω] [Fintype I]

noncomputable def familyRetained (A : I→Set Ω) (x : Ω) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => x∈A i)

theorem measurableSet_large_count (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (k : ℕ) :
    MeasurableSet {x : Ω | k ≤ (familyRetained A x).card} := by
  classical
  let P := (Finset.univ : Finset I).powersetCard k
  have eq : {x : Ω | k ≤ (familyRetained A x).card}
      = ⋃ T ∈ P, ⋂ i ∈ T, A i := by
    ext x
    change (k≤((Finset.univ : Finset I).filter (fun i => x∈A i)).card) ↔ _
    constructor
    · intro hx
      rcases Finset.exists_subset_card_eq hx with ⟨T, hT, hTk⟩
      exact Set.mem_iUnion.2 ⟨T,Set.mem_iUnion.2 ⟨Finset.mem_powersetCard.2
        ⟨Finset.subset_univ _,hTk⟩,Set.mem_iInter.2 fun i => Set.mem_iInter.2
        fun hi => (Finset.mem_filter.1 (hT hi)).2⟩⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨T,hT⟩
      rcases Set.mem_iUnion.1 hT with ⟨p,hT⟩
      rw [←(Finset.mem_powersetCard.1 p).2]
      apply Finset.card_le_card
      intro i hi
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
        Set.mem_iInter.1 (Set.mem_iInter.1 hT i) hi⟩
  rw [eq]
  exact MeasurableSet.biUnion P.countable_toSet (fun T _ =>
    MeasurableSet.biInter T.countable_toSet (fun i _ => hA i))

/-- A sparse binomial bound applies even when the tested neighbor set
depends on an independent random row coordinate. -/
theorem conditional_row_tail (σ : Measure S) [IsProbabilityMeasure σ]
    (E : Set (S×S)) (em : MeasurableSet E) (p : ℝ)
    (each : ∀ a, σ.real ((fun b => (a,b)) ⁻¹' E)≤p) (k : ℕ) :
    let τ := Measure.pi (fun _ : I => σ)
    (σ.prod τ) {z : S×(I→S) | k≤(retained ((fun b => (z.1,b)) ⁻¹' E) z.2).card}
      ≤ ENNReal.ofReal (Real.exp (2*(Fintype.card I:ℝ)*p)/(2:ℝ)^k) := by
  classical
  intro τ
  let B := {z : S×(I→S) | k≤(retained ((fun b => (z.1,b)) ⁻¹' E) z.2).card}
  have Bm : MeasurableSet B := by
    apply measurableSet_large_count (fun i => (fun z : S×(I→S) => (z.1,z.2 i)) ⁻¹' E)
    intro i
    exact (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)) em
  change (σ.prod τ) B ≤ _
  rw [Measure.prod_apply Bm]
  calc
    _ ≤ ∫⁻ _ : S, ENNReal.ofReal (Real.exp (2*(Fintype.card I:ℝ)*p)/(2:ℝ)^k) ∂σ := by
      apply lintegral_mono
      intro a
      let A := (fun b => (a,b)) ⁻¹' E
      let D := {y : I→S | k≤(retained A y).card}
      change τ D ≤ _
      have h := retained_upper_tail_exp (I:=I) σ A k
      change (τ D).toReal ≤ _ at h
      have a' : Real.exp (2*(Fintype.card I:ℝ)*(σ.real A)) ≤ Real.exp (2*(Fintype.card I:ℝ)*p) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (each a) (by positivity))
      have h' := ENNReal.ofReal_le_ofReal (h.trans (div_le_div_of_nonneg_right a' (by positivity)))
      rwa [ENNReal.ofReal_toReal (measure_ne_top τ _)] at h'
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

theorem fixed_sample_row_tail (σ : Measure S) [IsProbabilityMeasure σ]
    (E : Set (S×S)) (em : MeasurableSet E) (p : ℝ)
    (each : ∀ a, σ.real ((fun b => (a,b)) ⁻¹' E)≤p)
    (n k : ℕ) (i : Fin (n+1)) :
    (Measure.pi (fun _ : Fin (n+1) => σ))
      {x : Fin (n+1)→S | k≤(retained ((fun b => (x i,b)) ⁻¹' E)
        (fun j : Fin n => x (i.succAbove j))).card}
      ≤ ENNReal.ofReal (Real.exp (2*(n:ℝ)*p)/(2:ℝ)^k) := by
  let B := {z : S×(Fin n→S) | k≤(retained ((fun b => (z.1,b)) ⁻¹' E) z.2).card}
  have Bm : MeasurableSet B := by
    apply measurableSet_large_count (fun j => (fun z : S×(Fin n→S) => (z.1,z.2 j)) ⁻¹' E)
    intro j
    exact (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd)) em
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => S) i
  change (Measure.pi (fun _ : Fin (n+1) => σ)) (e ⁻¹' B) ≤ _
  have h := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => σ) i
  rw [h.measure_preimage Bm.nullMeasurableSet]
  simpa only [Fintype.card_fin] using conditional_row_tail (I:=Fin n) σ E em p each k

#print axioms fixed_sample_row_tail
end RobustFolkman.GeometricGap
