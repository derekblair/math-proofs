import TriangleCutContinuity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Set
open scoped ENNReal

namespace SparseHalfGraphon
variable {X : Type*} [MeasurableSpace X]

noncomputable def reweight (μ : Measure X) (f : X→ℝ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (f x))

lemma reweight_le (μ : Measure X) (f : X→ℝ) (hf : ∀ x, f x≤1) :
    reweight μ f ≤ μ := by
  calc
    reweight μ f ≤ μ.withDensity (1 : X→ℝ≥0∞) := by
      apply withDensity_mono
      exact ae_of_all _ (fun x => by simpa using ENNReal.ofReal_le_ofReal (hf x))
    _ = μ := withDensity_one

lemma reweight_ac (μ : Measure X) (f : X→ℝ) : reweight μ f ≪ μ :=
  withDensity_absolutelyContinuous _ _

lemma reweight_integral (μ : Measure X) (f : X→ℝ) (hf : Measurable f)
    (hf₀ : ∀ x, 0≤f x) (g : X→ℝ) :
    (∫ x, g x ∂reweight μ f) = ∫ x, f x*g x ∂μ := by
  unfold reweight
  rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) g]
  simp [ENNReal.toReal_ofReal,hf₀,smul_eq_mul]

lemma reweight_mass (μ : Measure X) (f : X→ℝ) (hf : Measurable f)
    (hf₀ : ∀ x, 0≤f x) :
    mass (reweight μ f)=∫ x, f x ∂μ := by
  have he := reweight_integral μ f hf hf₀ (fun _ => 1)
  simpa [integral_const,mass,smul_eq_mul] using he

/-- Bilinear energy integrated against two arbitrary fractional allocations. -/
noncomputable def energyPair (μ : Measure X) (K : Kernel X) (f g : X→ℝ) : ℝ :=
  ∫ z, f z.1*g z.2*K.W z ∂μ.prod μ

lemma reweight_energy (μ : Measure X) [IsFiniteMeasure μ] (K : Kernel X)
    (f g : X→ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf₀ : ∀ x, 0≤f x) (hg₀ : ∀ x, 0≤g x)
    (_hf₁ : ∀ x, f x≤1) (_hg₁ : ∀ x, g x≤1) :
    (∫ z, K.W z ∂(reweight μ f).prod (reweight μ g))=energyPair μ K f g := by
  unfold reweight energyPair
  rw [prod_withDensity hf.ennreal_ofReal hg.ennreal_ofReal]
  have hm : Measurable (fun z : X×X => ENNReal.ofReal (f z.1) * ENNReal.ofReal (g z.2)) :=
    (hf.ennreal_ofReal.comp measurable_fst).mul (hg.ennreal_ofReal.comp measurable_snd)
  rw [integral_withDensity_eq_integral_toReal_smul hm
      (ae_of_all _ (fun z => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)) K.W]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by simp [ENNReal.toReal_mul,ENNReal.toReal_ofReal,hf₀,hg₀,smul_eq_mul])

theorem mantel_allocation (μ : Measure X) [IsFiniteMeasure μ] (K : Kernel X)
    (f : X→ℝ) (hf : Measurable f) (hf₀ : ∀ x, 0≤f x) (hf₁ : ∀ x, f x≤1)
    (htri : ∀ᵐ z ∂(μ.prod μ).prod μ, triangle K z=0) :
    energyPair μ K f f/2≤(∫ x, f x ∂μ)^2/4 := by
  let ν := reweight μ f
  have : IsFiniteMeasure ν := isFiniteMeasure_of_le μ (reweight_le μ f hf₁)
  have hd := mantel_submeasure μ (ν:=ν) (reweight_ac μ f) K htri
  have hW : Integrable K.W (ν.prod ν) :=
    integrable_bounded _ K.measurable_W K.nonneg K.le_one
  rw [← reweight_mass μ f hf hf₀]
  have ht : energyPair μ K f f=density ν K := by
    rw [← reweight_energy μ K f f hf hf hf₀ hf₀ hf₁ hf₁]
    exact integral_prod K.W hW
  rw [ht]
  exact hd

#print axioms reweight_energy
#print axioms mantel_allocation
end SparseHalfGraphon
