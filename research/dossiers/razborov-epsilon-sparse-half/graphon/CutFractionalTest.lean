import CutRowControl
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set
open scoped ENNReal

namespace SparseHalfGraphon
variable {X : Type*} [MeasurableSpace X]

/-- A signed set-integral bound stays the same against any measurable
fractional selector. The two-sided Fubini proof is the layer-cake argument. -/
theorem bounded_test (μ : Measure X) [IsFiniteMeasure μ]
    (u f : X→ℝ) (hu : Measurable u) (hf : Measurable f)
    (C ε : ℝ) (huC : ∀ x, |u x|≤C)
    (hf₀ : ∀ x, 0≤f x) (hf₁ : ∀ x, f x≤1)
    (h : ∀ S : Set X, MeasurableSet S → |∫ x in S, u x ∂μ|≤ε) :
    |∫ x, u x*f x ∂μ|≤ε := by
  let ν := volume.restrict (Ioc (0:ℝ) 1)
  have hν : ν.real univ=1 := by
    simp [ν,Real.volume_real_Ioc]
  have : IsFiniteMeasure ν := ⟨by simp [ν,Real.volume_Ioc]⟩
  let Z : Set (X×ℝ) := {z | z.2≤f z.1}
  have hZ : MeasurableSet Z := measurableSet_le measurable_snd (hf.comp measurable_fst)
  let F : X×ℝ→ℝ := Z.indicator (fun z => u z.1)
  have im : Integrable F (μ.prod ν) := by
    apply Integrable.of_bound ((hu.comp measurable_fst).indicator hZ).aestronglyMeasurable C
    apply ae_of_all
    intro z
    have hC : 0≤C := (abs_nonneg _).trans (huC z.1)
    by_cases hz : z∈Z
    · simpa [F,Set.indicator_of_mem hz,Real.norm_eq_abs] using huC z.1
    · simpa [F,Set.indicator_of_notMem hz] using hC
  have hrow (x : X) : (∫ t, F (x,t) ∂ν)=u x*f x := by
    have hfun : (fun t => F (x,t)) = (Iic (f x)).indicator (fun _ => u x) := by
      funext t
      rfl
    rw [hfun,integral_indicator_const (u x) measurableSet_Iic,smul_eq_mul]
    have hs : Iic (f x) ∩ Ioc (0:ℝ) 1 = Ioc 0 (f x) := by
      ext t
      simp only [mem_inter_iff,mem_Iic,mem_Ioc]
      exact ⟨fun ⟨h₁,h₂,_⟩ => ⟨h₂,h₁⟩,fun ⟨h₁,h₂⟩ => ⟨h₂,h₁,h₂.trans (hf₁ x)⟩⟩
    unfold ν
    rw [measureReal_restrict_apply measurableSet_Iic,hs,Real.volume_real_Ioc_of_le (hf₀ x)]
    ring
  have hcol (t : ℝ) : (∫ x, F (x,t) ∂μ)=∫ x in {x | t≤f x}, u x ∂μ := by
    have he : (fun x => F (x,t)) = {x | t≤f x}.indicator u := by
      funext x
      rfl
    rw [he,integral_indicator (measurableSet_le measurable_const hf)]
  have hF : (∫ x, u x*f x ∂μ) = ∫ t, ∫ x, F (x,t) ∂μ ∂ν := by
    rw [← integral_prod_symm F im,integral_prod F im]
    simp_rw [hrow]
  have hh (t : ℝ) : |∫ x, F (x,t) ∂μ|≤ε := by
    rw [hcol]
    exact h _ (measurableSet_le measurable_const hf)
  rw [hF,abs_le]
  constructor
  · have hb := integral_mono (integrable_const (μ := ν) (-ε)) im.integral_prod_right
      (fun t => (abs_le.mp (hh t)).1)
    simpa [integral_const,hν,smul_eq_mul] using hb
  · have hb := integral_mono im.integral_prod_right (integrable_const (μ := ν) ε)
      (fun t => (abs_le.mp (hh t)).2)
    simpa [integral_const,hν,smul_eq_mul] using hb

#print axioms bounded_test
end SparseHalfGraphon
