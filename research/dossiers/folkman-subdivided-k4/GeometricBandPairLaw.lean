import GeometricBandBadMixture
import GeometricCapProbability
import Mathlib.MeasureTheory.Measure.WithDensity

namespace RobustFolkman.GeometricGap
open MeasureTheory Set WithLp
open scoped ENNReal InnerProductSpace
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]

theorem band_residual_pair_mass (m : ℕ) (dim : Module.finrank ℝ W=m+2)
    (H : Set (I→ℝ)) (hm : MeasurableSet H)
    (B : Set (UnitSphere W×UnitSphere W)) (Bm : MeasurableSet B) :
    let σ := uniformSphere (volume : Measure (SphereAmbient I W))
    let A := sphereCoord ⁻¹' H
    let τ := uniformSphere (volume : Measure W)
    σ A≠0 →
    (σ.prod σ) ((Prod.map sphereResidual sphereResidual) ⁻¹' B ∩ (A×ˢ A)) =
      (σ A)^2*(τ.prod τ) B := by
  intro σ A τ a0
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  letI : IsProbabilityMeasure (condOn σ A) := condOn_probability σ A a0 (measure_ne_top σ _)
  have law := conditioned_residual_uniform (I:=I) (W:=W) m dim H hm a0
  have f := law.prod law
  rw [←Measure.restrict_apply (f.measurable Bm),←Measure.prod_restrict,
    ←unnormalize_condOn σ A a0 (measure_ne_top σ _),
    Measure.prod_smul_left,Measure.prod_smul_right,Measure.smul_apply,Measure.smul_apply,smul_eq_mul,
    smul_eq_mul,f.measure_preimage Bm.nullMeasurableSet]
  ring

def pairCap (t : ℝ) : Set (UnitSphere W×UnitSphere W) :=
  {z | t≤⟪z.1.val,z.2.val⟫_ℝ}

theorem pairCap_measurable (t : ℝ) : MeasurableSet (pairCap (W:=W) t) :=
  measurableSet_le measurable_const
    ((continuous_subtype_val.comp continuous_fst).inner (𝕜:=ℝ)
      (continuous_subtype_val.comp continuous_snd)).measurable

theorem pairCap_mass (t : ℝ) (a : UnitSphere W) :
    let τ := uniformSphere (volume : Measure W)
    (τ.prod τ) (pairCap t)=τ (capPoints t a) := by
  intro τ
  letI : IsProbabilityMeasure τ := uniformSphere_isProbability _
  rw [Measure.prod_apply (pairCap_measurable t)]
  calc
    _ = ∫⁻ _ : UnitSphere W, τ (capPoints t a) ∂τ := by
      apply lintegral_congr
      intro x
      exact capPoints_mass_root_constant t x a
    _ = _ := by rw [lintegral_const,measure_univ,mul_one]

theorem pairCap_gap_mass (n : ℕ) (dim : Module.finrank ℝ W=n+3)
    (t s ε : ℝ) (tp : 0<t) (ts : t≤1/8) (r3 : 3≤(n:ℝ)/2)
    (dense : 1≤4*((n:ℝ)/2)*t^2) (s0 : 0≤s) (st : s≤t)
    (small : (4*((n:ℝ)/2)*t*s)*Real.exp (3+4*((n:ℝ)/2)*t*s)≤ε)
    (a : UnitSphere W) :
    let τ := uniformSphere (volume : Measure W)
    (τ.prod τ).real (pairCap (t-s)\pairCap t)≤ε*τ.real (capPoints t a) := by
  intro τ
  letI : IsProbabilityMeasure τ := uniformSphere_isProbability _
  have h : (τ.prod τ) (pairCap (t-s)\pairCap t)=τ (capPoints (t-s) a\capPoints t a) := by
    have le : pairCap (W:=W) t⊆pairCap (t-s) := by
      intro z hz
      have h : t≤⟪z.1.val,z.2.val⟫_ℝ := hz
      exact (sub_le_self _ s0).trans h
    have le' : capPoints t a⊆capPoints (t-s) a := by
      intro z hz
      have h : t≤⟪a.val,z.val⟫_ℝ := hz
      exact (sub_le_self _ s0).trans h
    rw [measure_diff le (pairCap_measurable t).nullMeasurableSet (measure_ne_top _ _),
      measure_diff le' (capPoints_measurable t a).nullMeasurableSet (measure_ne_top _ _),
      pairCap_mass (t-s) a,pairCap_mass t a]
  unfold Measure.real
  rw [h]
  exact cap_threshold_gap_mass n dim t s ε tp ts r3 dense s0 st small a

#print axioms band_residual_pair_mass
#print axioms pairCap_gap_mass
end RobustFolkman.GeometricGap
