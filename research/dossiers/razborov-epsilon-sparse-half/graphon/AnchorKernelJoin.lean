import SignatureAllocation

open Set MeasureTheory SparseHalfGraphon
open scoped ENNReal
namespace SparseHalfCountableEndpoint
variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

theorem energy_as_load (K : Kernel X) (f g : X→ℝ) (hf : BMeas f) (hg : BMeas g) :
    energyPair μ K f g=∫ x, f x*load μ K g x ∂μ := by
  unfold energyPair load
  rw [integral_prod _ (energy_integrable μ K hf hg)]
  apply integral_congr_ae
  filter_upwards with x
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  ring

/-- Glue an anchor fill measured in scale-ten units to an outside fill.
Only the precise cross load on the anchor is needed; both self energies
must vanish. The normalized cost is divided by one hundred. -/
theorem join_anchor (K : Kernel X) (A : Set X) (hA : MeasurableSet A)
    (f g L : X→ℝ) (b C : ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hnf : ∀ x,0≤f x ∧ f x≤1) (hng : ∀ x,0≤g x ∧ g x≤1)
    (gz : ∀ x∈A, g x=0)
    (aeA : ∀ᵐ z ∂(μ.restrict A).prod (μ.restrict A), K.W z=0)
    (g0 : energyPair μ K g g=0)
    (fm : (∫ x,f x ∂((10:ℝ≥0∞) • μ.restrict A))=b)
    (gm : (∫ x,g x ∂μ)=(5-b)/10)
    (loadEq : ∀ᵐ x ∂μ.restrict A, load μ K g x=L x/10)
    (fc : (∫ x,L x*f x ∂((10:ℝ≥0∞) • μ.restrict A))≤C) :
    ∃ H : Half μ, halfEnergy μ K H≤C/100 := by
  let F := A.indicator f
  have Fm : Measurable F := hf.indicator hA
  have Fb x : 0≤F x ∧ F x≤1 := by
    by_cases h : x∈A <;> simp [F,h,hnf x]
  have bF := BMeas.of_unit Fm (fun x=> (Fb x).1) (fun x=> (Fb x).2)
  have bg := BMeas.of_unit hg (fun x=> (hng x).1) (fun x=> (hng x).2)
  have mF : (∫ x,F x ∂μ)=b/10 := by
    rw [integral_smul_measure] at fm
    change _ = b at fm
    norm_num at fm
    unfold F
    rw [integral_indicator hA]
    linarith
  have f0 : energyPair μ K F F=0 := by
    rw [←reweight_energy μ K F F Fm Fm (fun x=>(Fb x).1) (fun x=>(Fb x).1)
      (fun x=>(Fb x).2) (fun x=>(Fb x).2)]
    have eq : reweight μ F = reweight (μ.restrict A) f := by
      ext s hs
      rw [reweight,withDensity_apply _ hs, reweight,withDensity_apply _ hs]
      change (∫⁻ x in s,ENNReal.ofReal (A.indicator f x) ∂μ) =
        ∫⁻ x in s, ENNReal.ofReal (f x) ∂μ.restrict A
      rw [Measure.restrict_restrict hs]
      rw [←lintegral_indicator hs,←lintegral_indicator (hs.inter hA)]
      apply lintegral_congr
      intro x
      by_cases ha : x∈A <;> by_cases ht : x∈s <;> simp [ha,ht]
    rw [eq]
    haveI : IsFiniteMeasure (reweight (μ.restrict A) f) :=
      isFiniteMeasure_of_le _ (reweight_le _ f (fun x => (hnf x).2))
    have absC : (reweight (μ.restrict A) f).prod (reweight (μ.restrict A) f) ≪
        (μ.restrict A).prod (μ.restrict A) :=
      (reweight_ac (μ.restrict A) f).prod (reweight_ac (μ.restrict A) f)
    exact integral_eq_zero_of_ae (absC.ae_le aeA)
  have cross : energyPair μ K F g≤C/100 := by
    rw [energy_as_load μ K F g bF bg]
    have ht : (fun x => F x * load μ K g x)=A.indicator (fun x=>f x*load μ K g x) := by
      ext x
      by_cases h : x∈A <;> simp [F,h]
    rw [ht,integral_indicator hA]
    have eq : (∫ x, f x*load μ K g x ∂μ.restrict A)=
        ∫ x, (L x*f x)/10 ∂μ.restrict A := by
      apply integral_congr_ae
      filter_upwards [loadEq] with x hh
      rw [hh]
      ring
    rw [eq,integral_div]
    rw [integral_smul_measure] at fc
    norm_num at fc
    linarith
  let H : Half μ :=
    ⟨F+g,Fm.add hg,
      fun x => add_nonneg (Fb x).1 (hng x).1,
      fun x => by
        by_cases hx : x∈A
        · simpa only [Pi.add_apply,gz x hx,add_zero] using (Fb x).2
        · simpa only [Pi.add_apply,F,indicator_of_notMem hx,zero_add] using (hng x).2,
      by
        change (∫ x,F x + g x ∂μ)=1/2
        rw [integral_add (bMeas_integrable μ bF) (bMeas_integrable μ bg),mF,gm]
        ring⟩
  refine ⟨H,?_⟩
  rw [halfEnergy_as_pair]
  change energyPair μ K (F+g) (F+g)/2≤C/100
  rw [energy_add_left μ K F g (F+g) bF bg (bF.add bg),
    energy_add_right μ K F F g bF bF bg,energy_add_right μ K g F g bg bF bg,
    energy_symm μ K g F,f0,g0]
  linarith

#print axioms join_anchor
end SparseHalfCountableEndpoint
