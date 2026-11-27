import Mathlib.Tactic

namespace LatticeShell

theorem directional_gap {len A x y : ℝ}
    (hx : x < (len - A) / 2) (hy : -y < (len - A) / 2) :
    A < len + y - x := by linarith

theorem enlargement_gap {ℓ e u v : ℝ} (he : 0 < e)
    (h : u < 1-e ∨ ℓ+e < u)
    (hlo : u-2*e/3 < v) (hhi : v < u+2*e/3) :
    v < 1 ∨ ℓ < v := by
  rcases h with h | h
  · left; linarith
  · right; linarith

theorem shell_alpha {ℓ t : ℝ} (hℓ : 1 ≤ ℓ) (ht : 0 < t)
    (ht2 : t ≤ 1/2) (h : 2*t^2 + ℓ*t = 1) :
    t/(ℓ+t) = t^2/(1-t^2) := by
  have hden : 0 < 1-t^2 := by nlinarith
  have hl : 0 < ℓ+t := by linarith
  apply (div_eq_div_iff hl.ne' hden.ne').2
  linear_combination -t*h

theorem shell_alpha_range {ℓ t : ℝ} (hℓ : 1 ≤ ℓ) (ht : 0 < t)
    (ht2 : t ≤ 1/2) : 0 < t/(ℓ+t) ∧ t/(ℓ+t) ≤ 1/3 := by
  have hl : 0 < ℓ+t := by linarith
  exact ⟨div_pos ht hl, (div_le_iff₀ hl).2 (by linarith)⟩

theorem shell_hessian {ℓ t : ℝ} (hℓ : 1 ≤ ℓ) (ht : 0 < t)
    (ht2 : t ≤ 1/2) (h : 2*t^2 + ℓ*t = 1) :
    1/(ℓ+t)^2 + (1+t^2)/(1-t^2)^2 =
      (1+2*t^2)/(1-t^2)^2 := by
  have hden : 0 < 1-t^2 := by nlinarith
  have hl : 0 < ℓ+t := by linarith
  have hcross : 1/(ℓ+t) = t/(1-t^2) := by
    apply (div_eq_div_iff hl.ne' hden.ne').2
    linear_combination -h
  have hs := congrArg (fun z : ℝ => z^2) hcross
  simp only [div_pow, one_pow] at hs
  rw [hs, ← add_div]
  congr 1
  ring

theorem shell_beats_axis {ℓ t : ℝ}
    (ht : 0 < t) (ht2 : t ≤ 1/2) (h : 2*t^2 + ℓ*t = 1) :
    ℓ^2 < (ℓ+t)^2*(1-t^2) := by
  have z : (ℓ+t)^2*(1-t^2) - ℓ^2 = 1-t^2-t^4 := by
    linear_combination (1 - ℓ*t) * h
  have hsq : t^2 ≤ (1/2 : ℝ)^2 := by nlinarith
  have hp : t^4 ≤ (1/4 : ℝ)^2 := by
    have ha := mul_nonneg (show 0 ≤ (1/4 : ℝ)-t^2 by norm_num at hsq ⊢; linarith)
      (show 0 ≤ (1/4 : ℝ)+t^2 by positivity)
    nlinarith
  nlinarith

end LatticeShell

#print axioms LatticeShell.directional_gap
#print axioms LatticeShell.shell_hessian
