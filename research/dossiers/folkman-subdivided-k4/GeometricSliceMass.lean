import GeometricSliceWeight
import GeometricShellIntegral

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped ENNReal

noncomputable def sliceMass (r a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Icc a b, ENNReal.ofReal (sliceWeight r x)

theorem sliceWeight_measurable (r : ℝ) (r0 : 0≤r) :
    Measurable (fun x => ENNReal.ofReal (sliceWeight r x)) := by
  unfold sliceWeight
  exact ((Real.continuous_rpow_const r0).measurable.comp
    (measurable_const.sub (measurable_id.pow_const 2))).ennreal_ofReal

private theorem slice_le (t r : ℝ) (tp : 0<t) (t1 : t≤1/8) : 0≤sliceWeight r t :=
  Real.rpow_nonneg (by nlinarith only [pow_le_pow_left₀ tp.le t1 2]) _

theorem slice_mass_cap_upper (r t : ℝ) (rp : 0<r) (tp : 0<t) (t1 : t<1) :
    sliceMass r t 1 ≤ ENNReal.ofReal (sliceWeight r t / (2*r*t)) := by
  let k := 2*r*t
  let a := sliceWeight r t
  have k0 : 0<k := by dsimp [k]; positivity
  have a0 : 0≤a := Real.rpow_nonneg (by
    nlinarith only [mul_pos (sub_pos.mpr t1) (show 0<1+t by positivity)] : 0≤1-t^2) r
  let F := fun x : ℝ => ENNReal.ofReal (Real.exp (-k*x))
  have fm : Measurable F := by dsimp [F]; fun_prop
  let g := fun x : ℝ => x + -t
  have gp : MeasurePreserving g volume volume := measurePreserving_add_right volume (-t)
  have set : g ⁻¹' Ici (0:ℝ) = Ici t := by ext x; simp [g]
  have shift := gp.setLIntegral_comp_preimage (measurableSet_Ici : MeasurableSet (Ici (0:ℝ))) fm
  rw [set] at shift
  unfold sliceMass
  calc
    _ ≤ ∫⁻ x in Icc t 1, ENNReal.ofReal a * F (g x) := by
      apply setLIntegral_mono (measurable_const.mul (fm.comp gp.measurable))
      intro x hx
      change _ ≤ ENNReal.ofReal a * ENNReal.ofReal (Real.exp (-k*g x))
      rw [←ENNReal.ofReal_mul a0]
      apply ENNReal.ofReal_le_ofReal
      have eq : -k*g x= -(2*r*t)*(x-t) := by dsimp [g,k]; ring
      rw [eq,mul_comm]
      exact slice_weight_upper_exp r t x rp tp.le hx.1 hx.2 t1
    _ ≤ ∫⁻ x in Ici t, ENNReal.ofReal a * F (g x) :=
      lintegral_mono_set (fun _ hx => hx.1)
    _ = _ := by
      have gm : Measurable (fun x => F (g x)) := fm.comp gp.measurable
      rw [lintegral_const_mul _ gm,shift]
      change ENNReal.ofReal a * (∫⁻ x : ℝ in Ici 0, ENNReal.ofReal (Real.exp (-k*x))) = _
      rw [lintegral_exp_halfline k 0 k0, mul_zero,Real.exp_zero,←ENNReal.ofReal_mul a0]
      congr 1
      dsimp [k,a]
      ring

theorem slice_mass_band_lower (r t W : ℝ) (r3 : 3≤r) (tp : 0<t) (t1 : t≤1/8)
    (d : 1≤4*r*t^2) (wide : 1/(4*r*t)≤W) :
    ENNReal.ofReal (Real.exp (-3)*sliceWeight r t/(4*r*t)) ≤ sliceMass r t (t+W) := by
  let w := 1/(4*r*t)
  have rp : 0<r := by linarith
  have wp : 0<w := by dsimp [w]; positivity
  unfold sliceMass
  refine le_trans ?_ (lintegral_mono_set (fun x hx => ⟨hx.1,by linarith only [hx.2,wide]⟩ :
    Icc t (t+w)⊆Icc t (t+W)))
  have lo : (∫⁻ _ : ℝ in Icc t (t+w), ENNReal.ofReal (Real.exp (-3)*sliceWeight r t)) ≤
    ∫⁻ x : ℝ in Icc t (t+w), ENNReal.ofReal (sliceWeight r x) := by
    apply setLIntegral_mono' measurableSet_Icc
    intro x hx
    exact ENNReal.ofReal_le_ofReal (slice_weight_thin_box r t x r3 tp t1 d hx.1 hx.2)
  rw [setLIntegral_const,Real.volume_Icc,add_sub_cancel_left,
    ←ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (slice_le t r tp t1))] at lo
  convert lo using 1
  congr 1
  dsimp [w]
  ring

theorem slice_mass_gap_upper (r t s : ℝ) (r0 : 0≤r) (tp : 0<t) (t1 : t≤1/8)
    (s0 : 0≤s) (st : s≤t) :
    sliceMass r (t-s) t ≤ ENNReal.ofReal (Real.exp (4*r*t*s)*sliceWeight r t*s) := by
  have h : (∫⁻ x in Icc (t-s) t, ENNReal.ofReal (sliceWeight r x)) ≤
      ∫⁻ _ : ℝ in Icc (t-s) t, ENNReal.ofReal (Real.exp (4*r*t*s)*sliceWeight r t) := by
    apply setLIntegral_mono' measurableSet_Icc
    intro x hx
    have e : sliceWeight r x≤sliceWeight r (t-s) := by
      apply Real.rpow_le_rpow (by
        have y := pow_le_pow_left₀ ((sub_nonneg.mpr st).trans hx.1) hx.2 2
        nlinarith only [y,pow_le_pow_left₀ tp.le t1 2]) _ r0
      have y := pow_le_pow_left₀ (sub_nonneg.mpr st) hx.1 2
      linarith only [y]
    exact ENNReal.ofReal_le_ofReal (e.trans (slice_weight_shift_upper r t s r0 tp t1 s0 st))
  rw [setLIntegral_const,Real.volume_Icc,sub_sub_cancel,
    ←ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (slice_le t r tp t1))] at h
  exact h

#print axioms slice_mass_cap_upper
#print axioms slice_mass_band_lower
#print axioms slice_mass_gap_upper
end RobustFolkman.GeometricGap
