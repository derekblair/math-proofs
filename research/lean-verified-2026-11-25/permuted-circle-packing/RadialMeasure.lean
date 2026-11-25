import PolarMeasure
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory Filter Set
open scoped ENNReal

namespace PermCircles
open Real

def polarRegion (a b R : ℝ) (L : ℝ → ℝ) : Set Point :=
  {p | p.2 ∈ Ioo a b ∧ p.1 ∈ Ioc (L p.2) R}

lemma domain_cap {R d : ℝ} (hR : 0 < R) (hd : 0 < d) (htop : d ≤ 2*R) :
    polarDomain (cap R (d,0)) =
      polarRegion (-arccos (d/(2*R))) (arccos (d/(2*R))) R (fun θ => d/(2*cos θ)) := by
  ext p
  rcases p with ⟨u,θ⟩
  change ((0<u ∧ -π<θ ∧ θ<π) ∧
    (sqDist (polar u θ) 0 ≤ R^2 ∧ sqDist (polar u θ) (d,0)<sqDist (polar u θ) 0)) ↔
    ((-arccos (d/(2*R)) < θ ∧ θ < arccos (d/(2*R))) ∧
      (d/(2*cos θ)<u ∧ u≤R))
  have ha0 : 0 < d/(2*R) := by positivity
  have ha1 : d/(2*R) ≤ 1 := (div_le_one (by positivity)).2 htop
  constructor
  · rintro ⟨⟨hu,hlo,hhi⟩,hs⟩
    obtain ⟨hr,hcap⟩ := (mem_cap_polar hR hd hu).1 hs
    have hc : 0 < cos θ := by by_contra! h; nlinarith [mul_nonpos_of_nonneg_of_nonpos hu.le h]
    have hmul := mul_le_mul_of_nonneg_right hr hc.le
    have hsh : d/(2*R) < cos θ := by
      apply (div_lt_iff₀ (show 0<2*R by positivity)).2
      linarith
    refine ⟨(angle_criterion ha0.le ha1 hlo hhi).1 hsh,?_⟩
    exact ⟨(div_lt_iff₀ (show 0<2*cos θ by positivity)).2 (by linarith),hr⟩
  · rintro ⟨⟨ha,hb⟩,hL,hr⟩
    have hmax := arccos_le_pi (d/(2*R))
    have hlo : -π<θ := by linarith
    have hhi : θ<π := by linarith
    have hcos := (angle_criterion ha0.le ha1 hlo hhi).2 ⟨ha,hb⟩
    have hcos0 := lt_trans ha0 hcos
    have hL0 : 0<d/(2*cos θ) := by positivity
    have hu := lt_trans hL0 hL
    have hm := (div_lt_iff₀ (show 0<2*cos θ by positivity)).1 hL
    exact ⟨⟨hu,hlo,hhi⟩,(mem_cap_polar hR hd hu).2 ⟨hr,by linarith⟩⟩

lemma lintegral_radial {l R : ℝ} (hl : 0 ≤ l) (h : l ≤ R) :
    (∫⁻ u in Ioc l R, ENNReal.ofReal u) = ENNReal.ofReal ((R^2-l^2)/2) := by
  have hi : IntegrableOn (fun x : ℝ => x) (Ioc l R) volume :=
    (continuous_id.intervalIntegrable l R).1
  have hn : 0 ≤ᵐ[volume.restrict (Ioc l R)] (fun x : ℝ => x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hl.trans hx.1.le
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn]
  rw [← intervalIntegral.integral_of_le h, integral_id]

lemma region_measurable (a b R : ℝ) {L : ℝ → ℝ} (hL : Measurable L) :
    MeasurableSet (polarRegion a b R L) := by
  apply (measurable_snd measurableSet_Ioo).inter
  exact (measurableSet_lt (hL.comp measurable_snd) measurable_fst).inter
    (measurableSet_le measurable_fst measurable_const)

lemma region_slice {a b R : ℝ} {L : ℝ → ℝ} (hL : Measurable L)
    (hLR : ∀ θ ∈ Ioo a b, 0 ≤ L θ ∧ L θ ≤ R) :
    (∫⁻ p in polarRegion a b R L, ENNReal.ofReal p.1) =
      ∫⁻ θ in Ioo a b, ENNReal.ofReal ((R^2-(L θ)^2)/2) := by
  rw [← lintegral_indicator (region_measurable a b R hL)]
  let f : Point → ℝ≥0∞ := (polarRegion a b R L).indicator (fun p => ENNReal.ofReal p.1)
  have hf : Measurable f := ((ENNReal.measurable_ofReal.comp measurable_fst).indicator
      (region_measurable a b R hL))
  change (∫⁻ p, f p ∂((volume : Measure ℝ).prod (volume : Measure ℝ))) = _
  rw [lintegral_prod_symm' f hf]
  rw [← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro θ
  by_cases hθ : θ ∈ Ioo a b
  · rw [indicator_of_mem hθ,← lintegral_radial (hLR θ hθ).1 (hLR θ hθ).2]
    rw [← lintegral_indicator measurableSet_Ioc]
    apply lintegral_congr
    intro u
    by_cases hu : u ∈ Ioc (L θ) R
    · have hh : (u,θ) ∈ polarRegion a b R L := ⟨hθ,hu⟩
      simp only [f,indicator_of_mem hh,indicator_of_mem hu]
    · have hh : (u,θ) ∉ polarRegion a b R L := fun h => hu h.2
      simp only [f,indicator_of_notMem hh,indicator_of_notMem hu]
  · rw [indicator_of_notMem hθ]
    have he (u : ℝ) : (u,θ) ∉ polarRegion a b R L := fun h => hθ h.1
    simp only [f,indicator_of_notMem (he _),lintegral_zero]

#print axioms domain_cap
#print axioms region_slice
end PermCircles
