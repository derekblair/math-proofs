import GeometricBandEdges
import GeometricSliceMass

namespace RobustFolkman.GeometricGap
open MeasureTheory Set WithLp
open scoped ENNReal
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]

theorem sphereHeight_measurable : Measurable (sphereHeight (W:=W)) :=
  (measurable_pi_apply 0).comp sphereCoord_measurable

/-- The exact probability of a height interval in the rank-one split.
All cap and shell comparisons below use the same normalization. -/
theorem spherical_height_interval (m : ℕ) (dim : Module.finrank ℝ W=m+2)
    (a b : ℝ) (a0 : -1≤a) (b1 : b≤1) :
    (uniformSphere (volume : Measure (SphereAmbient (Fin 1) W))) (sphereHeight ⁻¹' Icc a b) =
    sliceMass ((m:ℝ)/2) a b / sliceMass ((m:ℝ)/2) (-1) 1 := by
  let r := (m:ℝ)/2
  let G : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (sliceWeight r x)
  have Gm : Measurable G := sliceWeight_measurable r (by positivity)
  let P : (Fin 1→ℝ) → ℝ := fun q => q 0
  have PP : MeasurePreserving P volume volume := by
    have h := volume_preserving_piUnique (fun _ : Fin 1 => ℝ)
    convert h using 1
    funext x
    rfl
  have pe : (projectionBall : Set (Fin 1→ℝ)) = P ⁻¹' Ioo (-1:ℝ) 1 := by
    ext q
    change (∑ i, q i ^ 2)<1 ↔ q 0∈Ioo (-1:ℝ) 1
    rw [Fin.sum_univ_one]
    constructor
    · intro h
      constructor <;> by_contra! z
      · have e := mul_nonneg (show 0≤ -1-q 0 by linarith only [z])
          (show 0≤1-q 0 by linarith only [z])
        nlinarith only [h,e]
      · have e := mul_nonneg (show 0≤q 0-1 by linarith only [z])
          (show 0≤q 0+1 by linarith only [z])
        nlinarith only [h,e]
    · intro h
      have e := mul_pos (show 0<1-q 0 by exact sub_pos.mpr h.2)
        (show 0<1+q 0 by linarith only [h.1])
      nlinarith only [e]
  have pow (q : Fin 1→ℝ) (hq : q ∈ projectionBall) :
      projectionFactor m q = G (P q) := by
    have nn : 0≤1-(q 0)^2 := by
      change (∑ i, q i ^ 2)<1 at hq
      rw [Fin.sum_univ_one] at hq
      linarith only [hq]
    unfold projectionFactor G sliceWeight P
    rw [Fin.sum_univ_one,Real.sqrt_eq_rpow,←Real.rpow_mul_natCast nn]
    congr 2
    dsimp [r]
    ring
  let g : (Fin 1→ℝ) → ℝ≥0∞ := (Icc a b).indicator (fun _ => 1) ∘ P
  have gm : Measurable g := (measurable_const.indicator measurableSet_Icc).comp PP.measurable
  have law := spherical_projection_probability (I:=Fin 1) (W:=W) m dim g gm
  change (∫⁻ u : UnitSphere (SphereAmbient (Fin 1) W),
    (Icc a b).indicator (fun _ => (1:ℝ≥0∞)) (sphereHeight u)
    ∂uniformSphere (volume : Measure (SphereAmbient (Fin 1) W))) = _ at law
  rw [lintegral_indicator_const_comp sphereHeight_measurable measurableSet_Icc,one_mul] at law
  rw [law]
  have D : (∫⁻ q in (projectionBall : Set (Fin 1→ℝ)), projectionFactor m q) =
      sliceMass r (-1) 1 := by
    rw [setLIntegral_congr_fun projectionBall_measurable pow,pe,
      PP.setLIntegral_comp_preimage measurableSet_Ioo Gm]
    unfold sliceMass
    rw [Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc]
  have N : (∫⁻ q in (projectionBall : Set (Fin 1→ℝ)), projectionFactor m q*g q) =
      sliceMass r a b := by
    have eq : (∫⁻ q in (projectionBall : Set (Fin 1→ℝ)), projectionFactor m q*g q) =
        ∫⁻ q in (projectionBall : Set (Fin 1→ℝ)), G (P q)*g q :=
      setLIntegral_congr_fun projectionBall_measurable (fun q hq => by rw [pow q hq])
    rw [eq,pe]
    let h := fun x => G x*(Icc a b).indicator (fun _ => (1:ℝ≥0∞)) x
    have hm : Measurable h := Gm.mul (measurable_const.indicator measurableSet_Icc)
    change (∫⁻ q in P ⁻¹' Ioo (-1:ℝ) 1, h (P q)) = _
    rw [PP.setLIntegral_comp_preimage measurableSet_Ioo hm,
      Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc : Ioo (-1:ℝ) 1 =ᵐ[volume] Icc (-1:ℝ) 1)]
    unfold h
    have i : (Icc a b)⊆Icc (-1:ℝ) 1 := fun _ p => ⟨a0.trans p.1,p.2.trans b1⟩
    have H : (∫⁻ x in Icc (-1:ℝ) 1, G x * (Icc a b).indicator (fun _ => (1:ℝ≥0∞)) x) =
        ∫⁻ x in Icc (-1:ℝ) 1, (Icc a b).indicator G x := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro x _
      by_cases hx : x∈Icc a b <;> simp [indicator_of_mem,indicator_of_notMem,hx]
    rw [H,lintegral_indicator measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc,
      inter_eq_left.mpr i]
    rfl
  rw [D,N]

#print axioms spherical_height_interval
end RobustFolkman.GeometricGap
