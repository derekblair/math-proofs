import CouplingFractional

open MeasureTheory Set Function
namespace SparseHalfGraphon

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma energy_gap_test (ν : Measure Y) [IsFiniteMeasure ν] (K J : Kernel Y)
    (ε : ℝ) (hcut : CutBound ν K J ε) (f g : Y→ℝ)
    (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ x, 0≤f x)
    (hf1 : ∀ x, f x≤1) (hg0 : ∀ x, 0≤g x) (hg1 : ∀ x, g x≤1) :
    |energyPair ν K f g-energyPair ν J f g|≤ε := by
  have h := cut_product_test ν K J ε hcut f g hf hg hf0 hf1 hg0 hg1
  have fB := BMeas.of_unit hf hf0 hf1
  have gB := BMeas.of_unit hg hg0 hg1
  let F : Y×Y→ℝ := fun z => f z.1*g z.2*K.W z
  let G : Y×Y→ℝ := fun z => f z.1*g z.2*J.W z
  have iF : Integrable F (ν.prod ν) := energy_integrable ν K fB gB
  have iG : Integrable G (ν.prod ν) := energy_integrable ν J fB gB
  have he : energyPair ν K f g-energyPair ν J f g =
      ∫ y, (∫ x, gapW K J (x,y)*f x ∂ν)*g y ∂ν := by
    unfold energyPair
    have iFG : Integrable (fun z => F z-G z) (ν.prod ν) := iF.sub iG
    rw [← integral_sub iF iG,integral_prod_symm _ iFG]
    apply integral_congr_ae
    apply ae_of_all
    intro y
    change (∫ x, F (x,y)-G (x,y) ∂ν)=(∫ x, gapW K J (x,y)*f x ∂ν)*g y
    rw [← integral_mul_const]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by dsimp [F,G,gapW]; ring)
  exact he ▸ h

/-- A cut approximation does not worsen under a common measure-preserving
pullback, even if the projection is very far from injective. -/
theorem cut_pull (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (p : X→Y)
    (hp : MeasurePreserving p μ ν) (K J : Kernel Y) (ε : ℝ)
    (hcut : CutBound ν K J ε) :
    CutBound μ (pullKernel K p hp.measurable) (pullKernel J p hp.measurable) ε := by
  intro S T hS hT
  let m := μ.restrict S
  let n := μ.restrict T
  let σ := m.map p
  let τ := n.map p
  have hs : σ≤ν := by
    change m.map p≤ν
    rw [← hp.map_eq]
    exact Measure.map_mono Measure.restrict_le_self hp.measurable
  have ht : τ≤ν := by
    change n.map p≤ν
    rw [← hp.map_eq]
    exact Measure.map_mono Measure.restrict_le_self hp.measurable
  let f := fraction ν σ
  let g := fraction ν τ
  let K' := pullKernel K p hp.measurable
  let J' := pullKernel J p hp.measurable
  have hf := fraction_meas ν σ
  have hg := fraction_meas ν τ
  have hf0 := fraction_nn ν σ
  have hg0 := fraction_nn ν τ
  have hf1 := fraction_le ν σ
  have hg1 := fraction_le ν τ
  have hfσ : reweight ν f=σ := reweight_fraction ν σ hs
  have hgτ : reweight ν g=τ := reweight_fraction ν τ ht
  have hI : Integrable (gapW K' J') (m.prod n) :=
    (integrable_bounded _ K'.measurable_W K'.nonneg K'.le_one).sub
      (integrable_bounded _ J'.measurable_W J'.nonneg J'.le_one)
  change |∫ x, ∫ y, gapW K' J' (x,y) ∂n ∂m|≤ε
  rw [← integral_prod _ hI]
  unfold gapW
  rw [integral_sub (integrable_bounded _ K'.measurable_W K'.nonneg K'.le_one)
    (integrable_bounded _ J'.measurable_W J'.nonneg J'.le_one)]
  rw [push_submeasure_energy K p hp.measurable m n,push_submeasure_energy J p hp.measurable m n]
  change |(∫ z, K.W z ∂σ.prod τ)-(∫ z, J.W z ∂σ.prod τ)|≤ε
  rw [← hfσ,← hgτ,reweight_energy ν K f g hf hg hf0 hg0 hf1 hg1,
    reweight_energy ν J f g hf hg hf0 hg0 hf1 hg1]
  exact energy_gap_test ν K J ε hcut f g hf hg hf0 hf1 hg0 hg1

#print axioms cut_pull
end SparseHalfGraphon
