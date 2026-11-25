import PolarMembership
import PlaneMeasure
import Mathlib.Analysis.SpecialFunctions.PolarCoord

open MeasureTheory Set
open scoped ENNReal

namespace PermCircles

def polarDomain (S : Set Point) : Set Point :=
  polarCoord.target ∩ polarCoord.symm ⁻¹' S

lemma polarDomain_measurable {S : Set Point} (hs : MeasurableSet S) : MeasurableSet (polarDomain S) :=
  polarCoord.open_target.measurableSet.inter (continuous_polarCoord_symm.measurable hs)

lemma polar_measure {S : Set Point} (hs : MeasurableSet S) :
    volume S = ∫⁻ p in polarDomain S, ENNReal.ofReal p.1 := by
  rw [← lintegral_indicator_one hs, ← lintegral_comp_polarCoord_symm]
  rw [← lintegral_indicator (polarDomain_measurable hs)]
  rw [← lintegral_indicator polarCoord.open_target.measurableSet]
  apply lintegral_congr
  intro p
  by_cases hp : p ∈ polarCoord.target
  · rw [indicator_of_mem hp]
    by_cases hq : polarCoord.symm p ∈ S
    · have hd : p ∈ polarDomain S := ⟨hp,hq⟩
      rw [indicator_of_mem hd, indicator_of_mem hq]
      simp only [smul_eq_mul,Pi.one_apply,mul_one]
    · have hd : p ∉ polarDomain S := fun h => hq h.2
      rw [indicator_of_notMem hd, indicator_of_notMem hq]
      simp only [smul_zero]
  · have hd : p ∉ polarDomain S := fun h => hp h.1
    rw [indicator_of_notMem hp,indicator_of_notMem hd]

lemma domain_disk (R : ℝ) (hR : 0 ≤ R) :
    polarDomain (disk R 0) = Ioc 0 R ×ˢ Ioo (-Real.pi) Real.pi := by
  ext p
  rcases p with ⟨u,θ⟩
  change ((_ < u ∧ _) ∧ sqDist (polar u θ) 0 ≤ R^2) ↔ _
  rw [polar_sq]
  change ((0<u ∧ -Real.pi<θ ∧ θ<Real.pi) ∧ u^2≤R^2) ↔
    (0<u ∧ u≤R) ∧ (-Real.pi<θ ∧ θ<Real.pi)
  constructor
  · rintro ⟨⟨hu,hlo,hhi⟩,hs⟩
    exact ⟨⟨hu,(sq_le_sq₀ hu.le hR).1 hs⟩,hlo,hhi⟩
  · rintro ⟨⟨hu,hr⟩,hlo,hhi⟩
    exact ⟨⟨hu,hlo,hhi⟩,(sq_le_sq₀ hu.le hR).2 hr⟩

lemma domain_shadow {R d : ℝ} (hR : 0 < R) (hd : 0 < d) (htop : d ≤ 2*R) :
    polarDomain (shadow R (d,0)) =
      Ioc 0 R ×ˢ Ioo (-Real.arccos (d/(2*R))) (Real.arccos (d/(2*R))) := by
  ext p
  rcases p with ⟨u,θ⟩
  change ((0<u ∧ -Real.pi<θ ∧ θ<Real.pi) ∧ radialShadow R (d,0) (polar u θ)) ↔ _
  have ha0 : 0 ≤ d/(2*R) := by positivity
  have ha1 : d/(2*R) ≤ 1 := (div_le_one (by positivity)).2 htop
  constructor
  · rintro ⟨⟨hu,hlo,hhi⟩,hs⟩
    obtain ⟨hr,ha⟩ := (mem_shadow_polar hR hd hu).1 hs
    exact ⟨⟨hu,hr⟩,(angle_criterion ha0 ha1 hlo hhi).1 ha⟩
  · rintro ⟨⟨hu,hr⟩,ha,hb⟩
    have hmax := Real.arccos_le_pi (d/(2*R))
    have hlo : -Real.pi<θ := by linarith
    have hhi : θ<Real.pi := by linarith
    exact ⟨⟨hu,hlo,hhi⟩,(mem_shadow_polar hR hd hu).2
      ⟨hr,(angle_criterion ha0 ha1 hlo hhi).2 ⟨ha,hb⟩⟩⟩

#print axioms polar_measure
#print axioms domain_shadow
end PermCircles
