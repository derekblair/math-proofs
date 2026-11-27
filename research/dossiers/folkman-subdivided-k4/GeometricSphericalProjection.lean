import GeometricProjectionProduct
import GeometricAngularIntegration

namespace RobustFolkman.GeometricGap
open MeasureTheory Set WithLp
open scoped ENNReal
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]

abbrev SphereAmbient (I W : Type*) [Fintype I] := WithLp 2 (EuclideanSpace ℝ I × W)

noncomputable def normalizedCoords (x : SphereAmbient I W) : I→ℝ :=
  fun i => (ofLp (ofLp x).1) i / ‖x‖

theorem normalizedCoords_measurable : Measurable (normalizedCoords (I:=I) (W:=W)) := by
  apply Measurable.of_eval
  intro i
  exact (((measurable_pi_apply i).comp (PiLp.volume_preserving_ofLp I).measurable).comp
    (measurable_fst.comp (volume_preserving_ofLp (EuclideanSpace ℝ I) W).measurable)).div measurable_norm

theorem normalizedCoords_smul (x : SphereAmbient I W) (a : ℝ) (ha : 0<a) :
    normalizedCoords (a • x) = normalizedCoords x := by
  funext i
  unfold normalizedCoords
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos ha]
  change (a*(ofLp (ofLp x).1) i)/(a*‖x‖)=(ofLp (ofLp x).1) i/‖x‖
  exact mul_div_mul_left _ _ ha.ne'

theorem norm_as_pairRadius (x : SphereAmbient I W) :
    ‖x‖ = pairRadius (ofLp (ofLp x).1, ‖(ofLp x).2‖) := by
  unfold pairRadius
  rw [← EuclideanSpace.real_norm_sq_eq]
  change ‖x‖ = Real.sqrt (‖WithLp.fst x‖^2+‖WithLp.snd x‖^2)
  rw [← WithLp.prod_norm_sq_eq_of_L2, Real.sqrt_sq (norm_nonneg _)]

theorem sphereAmbient_finrank :
    Module.finrank ℝ (SphereAmbient I W) = Fintype.card I + Module.finrank ℝ W := by
  rw [(WithLp.linearEquiv 2 ℝ (EuclideanSpace ℝ I × W)).finrank_eq,
    Module.finrank_prod, finrank_euclideanSpace]

theorem normalizedCoords_sphere (x : UnitSphere (SphereAmbient I W)) :
    normalizedCoords x.val = ofLp (ofLp x.val).1 := by
  have h : ‖x.val‖=1 := by simpa [Metric.mem_sphere,dist_zero_right] using x.property
  funext i
  change (ofLp (ofLp x.val).1) i/‖x.val‖=(ofLp (ofLp x.val).1) i
  rw [h,div_one]

/-- Orthogonal coordinate density up to an explicit sphere-volume scale.
The common radial integral cancels exactly, not asymptotically. -/
theorem spherical_projection_unnormalized (m : ℕ)
    (dim : Module.finrank ℝ W=m+2)
    (g : (I→ℝ)→ℝ≥0∞) (gm : Measurable g)
    (h : ℝ→ℝ≥0∞) (hm : Measurable h)
    (h0 : (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^(Fintype.card I+m+1))*h r) ≠ 0)
    (ht : (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^(Fintype.card I+m+1))*h r) ≠ ∞) :
    (∫⁻ x : UnitSphere (SphereAmbient I W), g (ofLp (ofLp x.val).1)
      ∂(volume : Measure (SphereAmbient I W)).toSphere) =
      (volume : Measure W).toSphere univ *
        ∫⁻ u in (projectionBall : Set (I→ℝ)), projectionFactor m u*g u := by
  letI : Nontrivial (SphereAmbient I W) :=
    (WithLp.linearEquiv 2 ℝ (EuclideanSpace ℝ I × W)).symm.injective.nontrivial
  let μ := (volume : Measure (SphereAmbient I W))
  let ω := (volume : Measure W)
  let G : SphereAmbient I W→ℝ≥0∞ := g ∘ normalizedCoords
  have Gi (w : SphereAmbient I W) (a : ℝ) (ha : 0<a) : G (a • w)=G w :=
    congrArg g (normalizedCoords_smul w a ha)
  have hA := lintegral_angular_radial μ G (gm.comp normalizedCoords_measurable) Gi h hm
  have hd : Module.finrank ℝ (SphereAmbient I W)-1=Fintype.card I+m+1 := by
    rw [sphereAmbient_finrank,dim]
    omega
  rw [hd] at hA
  have hG (u : UnitSphere (SphereAmbient I W)) : G u.val = g (ofLp (ofLp u.val).1) :=
    congrArg g (normalizedCoords_sphere u)
  simp_rw [hG] at hA
  let E : SphereAmbient I W→((I→ℝ)×W) := fun x => (ofLp (ofLp x).1,(ofLp x).2)
  have eV : MeasurePreserving E μ ((volume : Measure (I→ℝ)).prod ω) :=
    ((PiLp.volume_preserving_ofLp I).prod (MeasurePreserving.id ω)).comp
      (volume_preserving_ofLp (EuclideanSpace ℝ I) W)
  let f : ((I→ℝ)×W)→ℝ≥0∞ :=
    fun p => g (pairProjection (p.1,‖p.2‖))*h (pairRadius (p.1,‖p.2‖))
  have fm : Measurable f :=
    ((gm.comp pairProjection_measurable).mul (hm.comp pairRadius_measurable)).comp
      (measurable_fst.prodMk (measurable_norm.comp measurable_snd))
  have hF (x : SphereAmbient I W) : f (E x) = G x*h ‖x‖ := by
    unfold f E G Function.comp pairProjection normalizedCoords
    rw [← norm_as_pairRadius x]
  have hB := eV.lintegral_comp fm
  simp_rw [hF] at hB
  have res := lintegral_product_projection ω m dim g gm h hm
  change (∫⁻ p, f p ∂((volume : Measure (I→ℝ)).prod ω)) = _ at res
  rw [hA] at hB
  rw [res,← mul_assoc] at hB
  exact le_antisymm ((ENNReal.mul_le_mul_iff_left h0 ht).mp hB.le)
    ((ENNReal.mul_le_mul_iff_left h0 ht).mp hB.ge)

#print axioms spherical_projection_unnormalized
end RobustFolkman.GeometricGap
