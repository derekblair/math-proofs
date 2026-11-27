import FiniteWeakRegularity
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

open MeasureTheory Set Function
open scoped ENNReal
namespace SparseHalfGraphon

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A pointwise [0,1] representative of a dominated measure's density. -/
noncomputable def fraction (ν σ : Measure Y) (y : Y) : ℝ :=
  (min 1 (σ.rnDeriv ν y)).toReal

lemma fraction_meas (ν σ : Measure Y) : Measurable (fraction ν σ) :=
  (measurable_const.min (Measure.measurable_rnDeriv σ ν)).ennreal_toReal

lemma fraction_nn (ν σ : Measure Y) (y : Y) : 0≤fraction ν σ y := ENNReal.toReal_nonneg
lemma fraction_le (ν σ : Measure Y) (y : Y) : fraction ν σ y≤1 := by
  unfold fraction
  simpa only [ENNReal.toReal_one] using
    (ENNReal.toReal_mono ENNReal.one_ne_top (min_le_left 1 (σ.rnDeriv ν y)))

theorem reweight_fraction (ν σ : Measure Y) [IsFiniteMeasure ν] (hh : σ≤ν) :
    reweight ν (fraction ν σ)=σ := by
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le ν hh
  calc
    reweight ν (fraction ν σ)=ν.withDensity (σ.rnDeriv ν) := by
      apply withDensity_congr_ae
      filter_upwards [Measure.rnDeriv_le_one_of_le hh] with y hy
      change σ.rnDeriv ν y≤(1:ℝ≥0∞) at hy
      change ENNReal.ofReal (min 1 (σ.rnDeriv ν y)).toReal=σ.rnDeriv ν y
      rw [min_eq_right hy,ENNReal.ofReal_toReal
        (ne_top_of_le_ne_top ENNReal.one_ne_top hy)]
    _=σ := Measure.withDensity_rnDeriv_eq σ ν hh.absolutelyContinuous

lemma map_mass (p : X→Y) (hp : Measurable p) (μ : Measure X) :
    mass (μ.map p)=mass μ := by
  unfold mass Measure.real
  rw [Measure.map_apply hp MeasurableSet.univ,Set.preimage_univ]

lemma half_pull {μ : Measure X} {ν : Measure Y} {p:X→Y} (hp : MeasurePreserving p μ ν)
    (H : Half ν) :
    ∃ G : Half μ, G.f=H.f ∘ p := by
  refine ⟨⟨H.f ∘ p,H.measurable_f.comp hp.measurable,fun x => H.nn (p x),
    fun x => H.le_one (p x),?_⟩,rfl⟩
  calc
    (∫ x, (H.f ∘ p) x ∂μ) = ∫ y, H.f y ∂μ.map p :=
      (integral_map hp.measurable.aemeasurable H.measurable_f.aestronglyMeasurable).symm
    _ = ∫ y, H.f y ∂ν := congrArg (fun m => ∫ y, H.f y ∂m) hp.map_eq
    _ = 1/2 := H.mass_half

/-- Fractional halves may be projected through a measure-preserving map
without altering cost. This is the non-injective direction needed for couplings. -/
theorem half_push_energy (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (p : X→Y) (hp : MeasurePreserving p μ ν)
    (K : Kernel Y) (H : Half μ) :
    ∃ G : Half ν, halfEnergy μ (pullKernel K p hp.measurable) H=halfEnergy ν K G := by
  let τ := reweight μ H.f
  let σ := τ.map p
  have ht : τ≤μ := reweight_le μ H.f H.le_one
  have : IsFiniteMeasure τ := isFiniteMeasure_of_le μ ht
  have hs : σ≤ν := by
    change τ.map p≤ν
    rw [← hp.map_eq]
    exact Measure.map_mono ht hp.measurable
  let f := fraction ν σ
  have hf : Measurable f := fraction_meas ν σ
  have hn : ∀ x, 0≤f x := fraction_nn ν σ
  have h1 : ∀ x, f x≤1 := fraction_le ν σ
  have hr : reweight ν f=σ := reweight_fraction ν σ hs
  have hm : (∫ x, f x ∂ν)=1/2 := by
    rw [← reweight_mass ν f hf hn,hr]
    change mass (τ.map p)=_
    rw [map_mass p hp.measurable,reweight_mass μ H.f H.measurable_f H.nn,H.mass_half]
  let G : Half ν := ⟨f,hf,hn,h1,hm⟩
  refine ⟨G,?_⟩
  rw [halfEnergy_as_pair,halfEnergy_as_pair]
  change energyPair μ (pullKernel K p hp.measurable) H.f H.f/2=
    energyPair ν K f f/2
  rw [← reweight_energy μ _ H.f H.f H.measurable_f H.measurable_f H.nn H.nn H.le_one H.le_one,
    ← reweight_energy ν K f f hf hf hn hn h1 h1,hr]
  change (∫ z, (pullKernel K p hp.measurable).W z ∂τ.prod τ)/2=
    (∫ z, K.W z ∂(τ.map p).prod (τ.map p))/2
  rw [push_submeasure_energy K p hp.measurable τ τ]

/-- Cut-limit couplings can change the underlying probability space.
The fractional optimum is invariant under either projection. -/
theorem beta_pull (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (p : X→Y) (hp : MeasurePreserving p μ ν)
    (hν : mass ν=1) (K : Kernel Y) :
    beta μ (pullKernel K p hp.measurable)=beta ν K := by
  have hμ : mass μ=1 := by rw [← map_mass p hp.measurable μ,hp.map_eq,hν]
  let J := pullKernel K p hp.measurable
  have bm : (range (halfEnergy μ J)).Nonempty := ⟨_,⟨constantHalf μ hμ,rfl⟩⟩
  have bn : (range (halfEnergy ν K)).Nonempty := ⟨_,⟨constantHalf ν hν,rfl⟩⟩
  apply le_antisymm
  · unfold beta
    apply le_csInf bn
    rintro _ ⟨H,rfl⟩
    obtain ⟨G,hG⟩ := half_pull hp H
    have hcost : halfEnergy μ J G=halfEnergy ν K H := by
      rw [halfEnergy_as_pair,halfEnergy_as_pair,hG]
      unfold J
      rw [pull_energy K p μ ν hp H.f H.f H.measurable_f H.measurable_f]
    rw [← hcost]
    exact csInf_le (range_bdd μ J) ⟨G,rfl⟩
  · unfold beta
    apply le_csInf bm
    rintro _ ⟨H,rfl⟩
    obtain ⟨G,hG⟩ := half_push_energy μ ν p hp K H
    rw [hG]
    exact csInf_le (range_bdd ν K) ⟨G,rfl⟩

#print axioms beta_pull
end SparseHalfGraphon
