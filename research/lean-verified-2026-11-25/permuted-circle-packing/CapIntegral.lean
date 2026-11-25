import DiskMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

open MeasureTheory Filter Set
open scoped ENNReal

namespace PermCircles
open Real

noncomputable def capSlice (R d θ : ℝ) : ℝ := (R^2-(d/(2*cos θ))^2)/2
noncomputable def capAnti (R d θ : ℝ) : ℝ := R^2*θ/2 - d^2*tan θ/8

lemma deriv_capAnti (R d θ : ℝ) (hc : cos θ ≠ 0) :
    HasDerivAt (capAnti R d) (capSlice R d θ) θ := by
  have hi := (((hasDerivAt_id θ).const_mul (R^2)).div_const 2).sub
    (((hasDerivAt_tan hc).const_mul (d^2)).div_const 8)
  convert hi using 1
  · rfl
  · unfold capSlice
    field_simp [hc] <;> ring

lemma cap_interval_integral (R d t : ℝ) (h0 : 0 ≤ t) (ht : t < π/2)
    (hc : d = 2*R*cos t) :
    ∫ θ in -t..t, capSlice R d θ = R^2/2*(2*t-sin (2*t)) := by
  have hab : -t ≤ t := by linarith
  have hpos : ∀ x ∈ Icc (-t) t, 0 < cos x := by
    intro x hx
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [hx.1]
    · linarith [hx.2]
  have hder : ∀ x ∈ uIcc (-t) t, HasDerivAt (capAnti R d) (capSlice R d x) x := by
    rw [uIcc_of_le hab]
    intro x hx
    exact deriv_capAnti R d x (ne_of_gt (hpos x hx))
  have hcont : ContinuousOn (capSlice R d) (uIcc (-t) t) := by
    rw [uIcc_of_le hab]
    unfold capSlice
    have hd : ContinuousOn (fun x : ℝ => d/(2*cos x)) (Icc (-t) t) :=
      continuousOn_const.div (continuous_cos.const_mul 2).continuousOn
        (fun x hx => ne_of_gt (mul_pos (by norm_num) (hpos x hx)))
    exact (continuousOn_const.sub (hd.pow 2)).div_const _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hcont.intervalIntegrable]
  unfold capAnti
  rw [tan_neg, hc, tan_eq_sin_div_cos, sin_two_mul]
  field_simp [(hpos t ⟨hab,le_rfl⟩).ne']
  ring

lemma shadow_volume_aligned {R d : ℝ} (hR : 0 < R) (hd : 0 < d) (htop : d ≤ 2*R) :
    volume (shadow R (d,0)) = ENNReal.ofReal (R^2*arccos (d/(2*R))) := by
  rw [polar_measure (shadow_measurable R _),domain_shadow hR hd htop]
  let t := arccos (d/(2*R))
  have he : Ioc 0 R ×ˢ Ioo (-t) t = polarRegion (-t) t R (fun _ => 0) := by
    ext z
    exact and_comm
  change (∫⁻ p in Ioc 0 R ×ˢ Ioo (-t) t, ENNReal.ofReal p.1) = _
  rw [he]
  rw [region_slice measurable_const (fun _ _ => ⟨le_rfl,hR.le⟩)]
  simp only [zero_pow (by decide : 2 ≠ 0),sub_zero,setLIntegral_const,Real.volume_Ioo]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

lemma cap_volume_aligned {R d : ℝ} (hR : 0 < R) (hd : 0 < d) (htop : d ≤ 2*R) :
    volume (cap R (d,0)) =
      ENNReal.ofReal (R^2/2*(2*arccos (d/(2*R))-sin (2*arccos (d/(2*R))))) := by
  let t := arccos (d/(2*R))
  have h0 : 0 ≤ t := arccos_nonneg _
  have ht : t < π/2 := arccos_lt_pi_div_two.mpr (by positivity)
  have hab : -t ≤ t := by linarith
  have hrat : 0 < d/(2*R) := by positivity
  have hcos : cos t = d/(2*R) := cos_arccos (by linarith) ((div_le_one (by positivity)).mpr htop)
  have hc : d = 2*R*cos t := by rw [hcos]; field_simp
  have hcI (θ : ℝ) (hθ : θ ∈ Icc (-t) t) : 0 < cos θ := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [hθ.1]
    · linarith [hθ.2]
  have hLR (θ : ℝ) (hθ : θ ∈ Ioo (-t) t) : 0 ≤ d/(2*cos θ) ∧ d/(2*cos θ) ≤ R := by
    have hp := hcI θ ⟨hθ.1.le,hθ.2.le⟩
    constructor
    · positivity
    · have hangle : |θ| ≤ t := (abs_le.mpr ⟨hθ.1.le,hθ.2.le⟩)
      have hcosle := cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) (by linarith [pi_pos] : t ≤ π) hangle
      rw [cos_abs] at hcosle
      apply (div_le_iff₀ (show 0<2*cos θ by positivity)).mpr
      rw [hc]
      nlinarith [mul_nonneg (show 0≤2*R by positivity) (show 0≤cos θ-cos t by linarith)]
  have hmeas : Measurable (fun θ : ℝ => d/(2*cos θ)) :=
    measurable_const.div (measurable_const.mul continuous_cos.measurable)
  rw [polar_measure (cap_measurable R _), domain_cap hR hd htop]
  change (∫⁻ p in polarRegion (-t) t R (fun θ => d/(2*cos θ)), ENNReal.ofReal p.1) = _
  rw [region_slice hmeas hLR]
  change (∫⁻ θ in Ioo (-t) t, ENNReal.ofReal (capSlice R d θ)) = _
  have hcont : ContinuousOn (capSlice R d) (uIcc (-t) t) := by
    rw [uIcc_of_le hab]
    unfold capSlice
    have hh : ContinuousOn (fun x : ℝ => d/(2*cos x)) (Icc (-t) t) :=
      continuousOn_const.div (continuous_cos.const_mul 2).continuousOn
        (fun x hx => ne_of_gt (mul_pos (by norm_num) (hcI x hx)))
    exact (continuousOn_const.sub (hh.pow 2)).div_const _
  have hI : IntegrableOn (capSlice R d) (Ioo (-t) t) volume :=
    hcont.intervalIntegrable.1.mono_set Ioo_subset_Ioc_self
  have hN : 0 ≤ᵐ[volume.restrict (Ioo (-t) t)] capSlice R d := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hl := hLR x hx
    change 0 ≤ (R^2-(d/(2*cos x))^2)/2
    have he := (sq_le_sq₀ hl.1 hR.le).2 hl.2
    linarith
  rw [← ofReal_integral_eq_lintegral_ofReal hI hN]
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hab]
  rw [cap_interval_integral _ _ _ h0 ht hc]

#print axioms cap_volume_aligned
#print axioms cap_interval_integral
#print axioms shadow_volume_aligned
end PermCircles
