import Rotation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

namespace PermCircles

open Real

noncomputable def polar (u θ : ℝ) : Point := (u*cos θ,u*sin θ)

lemma polar_sq (u θ : ℝ) : sqDist (polar u θ) 0 = u^2 := by
  simp [sqDist,polar]
  linear_combination u^2*(cos_sq_add_sin_sq θ)

lemma polar_scaled (u θ t : ℝ) : t • polar u θ = polar (t*u) θ := by
  apply Prod.ext <;> simp [polar,mul_assoc]

lemma angle_criterion {a θ : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hlo : -π < θ) (hhi : θ < π) :
    a < cos θ ↔ -arccos a < θ ∧ θ < arccos a := by
  have ha := cos_arccos (by linarith : -1 ≤ a) ha1
  have ht0 : 0 ≤ arccos a := arccos_nonneg a
  have ht1 : arccos a ≤ π := arccos_le_pi a
  have hθ : |θ| ≤ π := abs_le.mpr ⟨hlo.le,hhi.le⟩
  have hc : cos |θ| = cos θ := cos_abs θ
  rw [← abs_lt]
  constructor
  · intro h
    by_contra! hle
    have he := cos_le_cos_of_nonneg_of_le_pi ht0 hθ hle
    rw [ha,hc] at he
    linarith
  · intro h
    have he := cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg θ) ht1 h
    rwa [ha,hc] at he

lemma mem_shadow_polar {R d u θ : ℝ} (hR : 0 < R) (hd : 0 < d)
    (hu : 0 < u) :
    radialShadow R (d,0) (polar u θ) ↔ u ≤ R ∧ d/(2*R) < cos θ := by
  unfold radialShadow
  rw [polar_sq, sqrt_sq hu.le, polar_scaled, div_mul_cancel₀ _ hu.ne']
  have hh := cap_aligned hd (polar R θ)
  rw [polar_sq] at hh
  rw [hh]
  simp only [polar, and_iff_right (sq_pos_of_pos hu), sq_le_sq₀ hu.le hR.le]
  constructor
  · rintro ⟨h1,h2⟩
    split_ands
    · exact h1
    · apply (div_lt_iff₀ (show 0<2*R by positivity)).2
      linarith
  · rintro ⟨h1,h2⟩
    constructor
    · exact h1
    · have hh := (div_lt_iff₀ (show 0<2*R by positivity)).1 h2
      linarith

lemma mem_cap_polar {R d u θ : ℝ} (hR : 0 < R) (hd : 0 < d) (hu : 0 < u) :
    (sqDist (polar u θ) 0 ≤ R^2 ∧ sqDist (polar u θ) (d,0)<sqDist (polar u θ) 0) ↔
    u ≤ R ∧ d/2 < u*cos θ := by
  rw [cap_aligned hd,polar_sq,sq_le_sq₀ hu.le hR.le]
  rfl

lemma half_width_bound {r R d : ℝ} (hr : 0 < r) (hR : 0 < R)
    (h : R^2=4*r^2/3) (hd : 2*r ≤ d) (hd2 : d ≤ 2*R) :
    0 ≤ arccos (d/(2*R)) ∧ 2*arccos (d/(2*R)) ≤ π/3 := by
  have hS : 0 < sqrt 3 := sqrt_pos.2 (by norm_num)
  have hS2 : (sqrt 3)^2=3 := sq_sqrt (by norm_num)
  have hs : (R*sqrt 3)^2 = (2*r)^2 := by
    rw [mul_pow,hS2,h]
    ring
  have he : R*sqrt 3 = 2*r :=
    (sq_eq_sq₀ (mul_nonneg hR.le hS.le) (by positivity)).mp hs
  have hh : sqrt 3/2 ≤ d/(2*R) := by
    apply (le_div_iff₀ (show 0<2*R by positivity)).2
    nlinarith
  constructor
  · exact arccos_nonneg _
  · have ht : arccos (d/(2*R)) ≤ π/6 := by
      have hy := arccos_le_pi (d/(2*R))
      by_contra! hh'
      have hm := cos_lt_cos_of_nonneg_of_le_pi (by positivity) hy hh'
      have hdp : 0 < d := lt_of_lt_of_le (by positivity) hd
      have htpos : 0 ≤ d/(2*R) := by positivity
      rw [cos_pi_div_six, cos_arccos (by linarith) ((div_le_one (by positivity)).mpr hd2)] at hm
      linarith
    linarith

#print axioms mem_shadow_polar
#print axioms half_width_bound
end PermCircles
