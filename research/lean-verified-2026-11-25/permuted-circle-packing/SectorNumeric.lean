import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

namespace PermCircles

open Real

lemma chord_sin {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π/3) :
    (θ / (π/3)) * (sqrt 3/2) ≤ sin θ := by
  have hp : 0 < π/3 := by positivity
  let t := θ/(π/3)
  have ht : 0 ≤ t := div_nonneg h0 hp.le
  have ht' : t ≤ 1 := (div_le_one hp).mpr h1
  have hw : (1-t)+t=1 := by ring
  have hP := strictConcaveOn_sin_Icc.concaveOn.2 (x:=0) (y:=π/3)
    ⟨le_rfl,pi_pos.le⟩ ⟨hp.le,by linarith [pi_pos]⟩ (sub_nonneg.mpr ht') ht hw
  have hm : t*(π/3)=θ := div_mul_cancel₀ _ hp.ne'
  simpa [smul_eq_mul,hm,sin_pi_div_three,t] using hP

lemma circle_cap_ratio {θ R : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π/3) :
    R^2/2*(θ-sin θ) ≤ (1-3*sqrt 3/(2*π))*(R^2/2*θ) := by
  have h := chord_sin h0 h1
  have hp : π ≠ 0 := pi_pos.ne'
  have he : (θ/(π/3))*(sqrt 3/2) = (3*sqrt 3/(2*π))*θ := by field_simp <;> ring
  rw [he] at h
  have hh : θ-sin θ ≤ (1-3*sqrt 3/(2*π))*θ := by linarith
  calc
    _ ≤ R^2/2*((1-3*sqrt 3/(2*π))*θ) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

lemma cell_constant (r R : ℝ) (hR : R^2=4*r^2/3) :
    π*R^2-(1-3*sqrt 3/(2*π))*(π*R^2) = 2*sqrt 3*r^2 := by
  rw [hR]
  have hp : π ≠ 0 := pi_pos.ne'
  field_simp
  ring

#print axioms circle_cap_ratio
#print axioms cell_constant
end PermCircles
