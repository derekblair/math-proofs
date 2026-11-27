import GeometricCapAveraging
import GeometricCapHeightTail
import GeometricGridApprox

namespace RobustFolkman.GeometricGap
open MeasureTheory Set WithLp
open scoped InnerProductSpace ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

def rootHeightStrip (a : UnitSphere E) (l u : ℝ) : Set (UnitSphere E) :=
  (fun z => ⟪a.val,z.val⟫_ℝ) ⁻¹' Icc l u

theorem rootHeightStrip_measurable (a : UnitSphere E) (l u : ℝ) :
    MeasurableSet (rootHeightStrip a l u) :=
  (continuous_const.inner (𝕜:=ℝ) continuous_subtype_val).measurable measurableSet_Icc

theorem root_height_interval (n : ℕ) (dim : Module.finrank ℝ E=n+3)
    (a : UnitSphere E) (l u : ℝ) (low : -1≤l) (hi : u≤1) :
    (uniformSphere (volume : Measure E)) (rootHeightStrip a l u) =
      sliceMass ((n:ℝ)/2) l u / sliceMass ((n:ℝ)/2) (-1) 1 := by
  obtain ⟨K,e,he,hD⟩ := root_shell_isometry a
  let W := ↥Kᗮ
  have D : Module.finrank ℝ W=n+2 := by dsimp [W]; omega
  letI : Nontrivial W := Module.nontrivial_of_finrank_pos (R:=ℝ) (by omega)
  letI : Nontrivial (SphereAmbient (Fin 1) W) := e.injective.nontrivial
  let B := sphereHeight (W:=W) ⁻¹' Icc l u
  have Bm : MeasurableSet B := sphereHeight_measurable measurableSet_Icc
  have pre : sphereTransport e ⁻¹' B=rootHeightStrip a l u := by
    ext z
    change sphereHeight (sphereTransport e z)∈Icc l u ↔ ⟪a.val,z.val⟫_ℝ∈Icc l u
    rw [he]
  have h := (sphereTransport_volume e).measure_preimage Bm.nullMeasurableSet
  rw [pre] at h
  exact h.trans (spherical_height_interval n D l u low hi)

theorem slice_interval_le_length (r l u : ℝ) (r0 : 0≤r) (l0 : -1≤l) (u1 : u≤1) :
    sliceMass r l u≤ENNReal.ofReal (u-l) := by
  unfold sliceMass
  calc
    _ ≤ ∫⁻ _ : ℝ in Icc l u, (1:ℝ≥0∞) := by
      apply setLIntegral_mono measurable_const
      intro x hx
      have z : |x|≤1 := abs_le.mpr ⟨l0.trans hx.1,hx.2.trans u1⟩
      have s := pow_le_pow_left₀ (abs_nonneg _) z 2
      rw [sq_abs,one_pow] at s
      have w : sliceWeight r x≤1 := Real.rpow_le_one (by linarith only [s])
        (by linarith only [sq_nonneg x]) r0
      simpa using (ENNReal.ofReal_le_ofReal w)
    _ = _ := by rw [setLIntegral_const,one_mul,Real.volume_Icc]

theorem slice_normalizer_pos_finite (r : ℝ) (r0 : 0≤r) :
    0<sliceMass r (-1) 1 ∧ sliceMass r (-1) 1≠∞ := by
  have hi := slice_interval_le_length r (-1) 1 r0 le_rfl le_rfl
  refine ⟨?_,ne_of_lt (hi.trans_lt ENNReal.ofReal_lt_top)⟩
  unfold sliceMass
  have l : (∫⁻ _ : ℝ in Icc 0 (1/2), ENNReal.ofReal ((3/4:ℝ)^r)) ≤
      ∫⁻ x in Icc 0 (1/2), ENNReal.ofReal (sliceWeight r x) := by
    apply setLIntegral_mono' measurableSet_Icc
    intro x hx
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow (by norm_num) _ r0
    have z := pow_le_pow_left₀ hx.1 hx.2 2
    nlinarith only [z]
  rw [setLIntegral_const,Real.volume_Icc,sub_zero] at l
  have p : 0<ENNReal.ofReal ((3/4:ℝ)^r)*ENNReal.ofReal (1/2) :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (by norm_num) _)).ne'
      (ENNReal.ofReal_pos.2 (by norm_num)).ne'
  refine p.trans_le (l.trans (lintegral_mono_set ?_))
  exact fun x hx => ⟨(by norm_num : (-1:ℝ)≤0).trans hx.1,hx.2.trans (by norm_num)⟩

theorem root_strip_real_bound (n : ℕ) (dim : Module.finrank ℝ E=n+3)
    (a : UnitSphere E) (l u : ℝ) (l0 : -1≤l) (u1 : u≤1) (lu : l≤u) :
    let r := (n:ℝ)/2
    let Z := (sliceMass r (-1) 1).toReal
    (uniformSphere (volume : Measure E)).real (rootHeightStrip a l u) ≤ (u-l)/Z := by
  intro r Z
  unfold Measure.real
  rw [root_height_interval n dim a l u l0 u1,ENNReal.toReal_div]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (slice_interval_le_length r l u (by positivity) l0 u1)
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr lu)] at h
  exact div_le_div_of_nonneg_right h ENNReal.toReal_nonneg

#print axioms root_strip_real_bound
end RobustFolkman.GeometricGap
