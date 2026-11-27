import GeometricSphericalStrip

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped InnerProductSpace ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

def pairHeightStrip (l u : ℝ) : Set (UnitSphere E×UnitSphere E) :=
  (fun z => ⟪z.1.val,z.2.val⟫_ℝ) ⁻¹' Icc l u

theorem pairHeightStrip_measurable (l u : ℝ) :
    MeasurableSet (pairHeightStrip (E:=E) l u) :=
  (((continuous_subtype_val.comp continuous_fst).inner (𝕜:=ℝ)
        (continuous_subtype_val.comp continuous_snd)).measurable) measurableSet_Icc

theorem pair_strip_real_bound (n : ℕ) (dim : Module.finrank ℝ E=n+3)
    (l u : ℝ) (l0 : -1≤l) (u1 : u≤1) (lu : l≤u) :
    let σ := uniformSphere (volume : Measure E)
    let Z := (sliceMass ((n:ℝ)/2) (-1) 1).toReal
    (σ.prod σ).real (pairHeightStrip l u) ≤ (u-l)/Z := by
  intro σ Z
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  let A := pairHeightStrip (E:=E) l u
  have Am : MeasurableSet A := pairHeightStrip_measurable l u
  have C0 : 0≤(u-l)/Z := div_nonneg (sub_nonneg.mpr lu) ENNReal.toReal_nonneg
  have h : (σ.prod σ) A ≤ ENNReal.ofReal ((u-l)/Z) := by
    rw [Measure.prod_apply Am]
    calc
      _ ≤ ∫⁻ _ : UnitSphere E, ENNReal.ofReal ((u-l)/Z) ∂σ := by
        apply lintegral_mono
        intro a
        change σ (rootHeightStrip a l u) ≤ _
        have b := root_strip_real_bound n dim a l u l0 u1 lu
        change (σ (rootHeightStrip a l u)).toReal ≤ (u-l)/Z at b
        have z := ENNReal.ofReal_le_ofReal b
        rwa [ENNReal.ofReal_toReal (measure_ne_top σ _)] at z
      _ = _ := by rw [lintegral_const, measure_univ, mul_one]
  change ((σ.prod σ) A).toReal ≤ _
  have k := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal C0] at k

#print axioms pair_strip_real_bound
end RobustFolkman.GeometricGap
