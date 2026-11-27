import GeometricPairStrip

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped InnerProductSpace ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem simple_slice_lower (n : ℕ) :
    ENNReal.ofReal ((1:ℝ)/4*((1:ℝ)/2)^n) ≤ sliceMass ((n:ℝ)/2) (1/4) (1/2) := by
  unfold sliceMass
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤1/4),mul_comm]
  calc
    _ = ∫⁻ _ : ℝ in Icc (1/4) (1/2), ENNReal.ofReal (((1:ℝ)/2)^n) := by
      rw [setLIntegral_const,Real.volume_Icc]
      norm_num
    _ ≤ _ := by
      apply setLIntegral_mono' measurableSet_Icc
      intro x hx
      apply ENNReal.ofReal_le_ofReal
      unfold sliceWeight
      have h : (1/2:ℝ)^n ≤ (1/2:ℝ)^((n:ℝ)/2) := by
        rw [←Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
          (by have hh : (0:ℝ)≤n := Nat.cast_nonneg n; linarith only [hh])
      apply h.trans
      apply Real.rpow_le_rpow (by norm_num) _ (by positivity)
      have x2 := pow_le_pow_left₀ (by linarith only [hx.1] : 0≤x) hx.2 2
      nlinarith only [x2]

theorem cap_simple_grid_lower (n : ℕ) (dim : Module.finrank ℝ E=n+3)
    (t : ℝ) (ts : t≤1/8) (a : UnitSphere E) :
    let σ := uniformSphere (volume : Measure E)
    let Z := (sliceMass ((n:ℝ)/2) (-1) 1).toReal
    (1/4:ℝ)*(1/2:ℝ)^n≤Z ∧ (1/8:ℝ)*(1/2:ℝ)^n≤σ.real (capPoints t a) := by
  intro σ Z
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  let L := sliceMass ((n:ℝ)/2) (1/4) (1/2)
  have l : ENNReal.ofReal ((1/4:ℝ)*(1/2:ℝ)^n)≤L := simple_slice_lower n
  have u := slice_interval_le_length ((n:ℝ)/2) (-1) 1 (by positivity) le_rfl le_rfl
  have top : sliceMass ((n:ℝ)/2) (-1) 1≠⊤ := ne_of_lt (u.trans_lt ENNReal.ofReal_lt_top)
  have LZ : L≤sliceMass ((n:ℝ)/2) (-1) 1 := by
    apply lintegral_mono_set
    intro x hx
    exact ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
  have lZ := ENNReal.toReal_mono top (l.trans LZ)
  rw [ENNReal.toReal_ofReal (by positivity)] at lZ
  refine ⟨lZ,?_⟩
  have Z2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top u
  rw [ENNReal.toReal_ofReal (by norm_num)] at Z2
  have Zp : 0<Z := (by positivity : 0<(1/4:ℝ)*(1/2:ℝ)^n).trans_le lZ
  have lL := ENNReal.toReal_mono (ne_of_lt (LZ.trans_lt (lt_top_iff_ne_top.2 top))) l
  rw [ENNReal.toReal_ofReal (by positivity)] at lL
  have G : rootHeightStrip a (1/4) (1/2) ⊆ capPoints t a := by
    intro x hx
    change ⟪a.val,x.val⟫_ℝ∈Icc (1/4:ℝ) (1/2:ℝ) at hx
    change t≤⟪a.val,x.val⟫_ℝ
    linarith only [hx.1,ts]
  have comp := ENNReal.toReal_mono (measure_ne_top σ _) (measure_mono (μ:=σ) G)
  rw [root_height_interval n dim a _ _ (by norm_num) (by norm_num),ENNReal.toReal_div] at comp
  change L.toReal/Z≤σ.real (capPoints t a) at comp
  refine le_trans ((le_div_iff₀ Zp).2 ?_) comp
  have h := mul_le_mul_of_nonneg_left Z2 (by positivity : 0≤(1/8:ℝ)*(1/2:ℝ)^n)
  exact (by nlinarith only [h,lL])

#print axioms cap_simple_grid_lower
end RobustFolkman.GeometricGap
