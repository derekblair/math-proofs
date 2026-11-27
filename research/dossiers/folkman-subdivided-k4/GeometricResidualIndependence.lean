import GeometricProjectionLaw

namespace RobustFolkman.GeometricGap
open MeasureTheory Set WithLp
open scoped ENNReal
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]

/-- A height test and an angular test factor already under product
Lebesgue measure whenever the remaining factors use only the radius. -/
theorem residual_angular_product (f : ((I→ℝ) × ℝ) → ℝ≥0∞) (fm : Measurable f)
    (A : W→ℝ≥0∞) (Am : Measurable A)
    (Ah : ∀ w (b:ℝ), 0<b → A (b • w)=A w) :
    (∫⁻ p : (I→ℝ)×W, A p.2 * f (p.1,‖p.2‖)) =
    (∫⁻ u : UnitSphere W, A u.val ∂uniformSphere (volume : Measure W)) *
      (∫⁻ p : (I→ℝ)×W, f (p.1,‖p.2‖)) := by
  let ω := (volume : Measure W)
  let α := (volume : Measure (I→ℝ))
  let H := fun p : (I→ℝ)×W => f (p.1,‖p.2‖)
  have Hm : Measurable H := fm.comp (measurable_fst.prodMk (measurable_norm.comp measurable_snd))
  let D := ∫⁻ u : UnitSphere W, A u.val ∂uniformSphere ω
  have hD : (∫⁻ u : UnitSphere W, A u.val ∂ω.toSphere) = D * ω.toSphere univ := by
    have nt : ω.toSphere univ≠∞ := measure_ne_top _ _
    have nz : ω.toSphere univ≠0 := fun e =>
      ω.toSphere_ne_zero (Measure.measure_univ_eq_zero.mp e)
    dsimp [D,uniformSphere]
    rw [lintegral_smul_measure,smul_eq_mul,mul_comm _ (ω.toSphere univ), ←mul_assoc,
      ENNReal.mul_inv_cancel nz nt,one_mul]
  have split (x : I→ℝ) :
      (∫⁻ w, A w * H (x,w) ∂ω) = D * (∫⁻ w, H (x,w) ∂ω) := by
    let h := fun r => f (x,r)
    have hm : Measurable h := fm.comp (measurable_const.prodMk measurable_id)
    have one := lintegral_angular_radial ω (fun _ => (1:ℝ≥0∞)) measurable_const
      (by intros; rfl) h hm
    simp only [one_mul,lintegral_const,MeasureTheory.measure_univ] at one
    have z := lintegral_angular_radial ω A Am Ah h hm
    change (∫⁻ w, A w * H (x,w) ∂ω) = _ at z
    rw [z,hD,mul_assoc]
    exact congrArg (D * ·) one.symm
  change (∫⁻ p, A p.2 * H p ∂α.prod ω) = D * (∫⁻ p, H p ∂α.prod ω)
  have HAm : Measurable (fun p : (I→ℝ)×W => A p.2 * H p) := (Am.comp measurable_snd).mul Hm
  rw [lintegral_prod _ HAm.aemeasurable,
    lintegral_prod _ Hm.aemeasurable]
  simp_rw [split]
  exact lintegral_const_mul D (Hm.lintegral_prod_right)

/-- In an orthogonal split of a uniform sphere, normalized first-block
coordinates are independent of every measurable test of residual angle. -/
theorem spherical_residual_angular_independence (m : ℕ)
    (dim : Module.finrank ℝ W=m+2)
    (g : (I→ℝ)→ℝ≥0∞) (gm : Measurable g)
    (A : W→ℝ≥0∞) (Am : Measurable A)
    (Ah : ∀ w (b:ℝ), 0<b → A (b • w)=A w) :
    (∫⁻ u : UnitSphere (SphereAmbient I W),
      A (ofLp u.val).2 * g (ofLp (ofLp u.val).1)
      ∂uniformSphere (volume : Measure (SphereAmbient I W))) =
    (∫⁻ v : UnitSphere W, A v.val ∂uniformSphere (volume : Measure W)) *
    (∫⁻ u : UnitSphere (SphereAmbient I W), g (ofLp (ofLp u.val).1)
      ∂uniformSphere (volume : Measure (SphereAmbient I W))) := by
  let μ := (volume : Measure (SphereAmbient I W))
  let B := fun x : SphereAmbient I W => g (normalizedCoords x)
  let A' := fun x : SphereAmbient I W => A (ofLp x).2
  let D := ∫⁻ u : UnitSphere W, A u.val ∂uniformSphere (volume : Measure W)
  let h := reciprocalRadial (Fintype.card I+m+1)
  have hm : Measurable h := reciprocalRadial_measurable _
  have mm : Measurable B := gm.comp normalizedCoords_measurable
  have ma : Measurable A' := Am.comp
    (measurable_snd.comp (volume_preserving_ofLp (EuclideanSpace ℝ I) W).measurable)
  have ai (x : SphereAmbient I W) (b : ℝ) (bp : 0<b) : A' (b • x)=A' x :=
    Ah (ofLp x).2 b bp
  have bi (x : SphereAmbient I W) (b : ℝ) (bp : 0<b) : B (b • x)=B x :=
    congrArg g (normalizedCoords_smul x b bp)
  letI : Nontrivial (SphereAmbient I W) :=
    (WithLp.linearEquiv 2 ℝ (EuclideanSpace ℝ I × W)).symm.injective.nontrivial
  have wrap (G : SphereAmbient I W → ℝ≥0∞) (Gm : Measurable G)
      (Gi : ∀ x (b:ℝ), 0<b → G (b • x)=G x) :
      (∫⁻ x, G x * h ‖x‖ ∂μ) = ∫⁻ u : UnitSphere (SphereAmbient I W), G u.val ∂μ.toSphere := by
    rw [lintegral_angular_radial μ G Gm Gi h hm]
    have d : Module.finrank ℝ (SphereAmbient I W)-1=Fintype.card I+m+1 := by
      rw [sphereAmbient_finrank,dim]
      omega
    rw [d,reciprocalRadial_integral,mul_one]
  let J : SphereAmbient I W → ((I→ℝ)×W) := fun x => (ofLp (ofLp x).1,(ofLp x).2)
  have jm : MeasurePreserving J μ volume :=
    ((PiLp.volume_preserving_ofLp I).prod (MeasurePreserving.id (volume : Measure W))).comp
      (volume_preserving_ofLp (EuclideanSpace ℝ I) W)
  let f : ((I→ℝ)×ℝ) → ℝ≥0∞ :=
    fun p => g (pairProjection p)*h (pairRadius p)
  have fm : Measurable f := (gm.comp pairProjection_measurable).mul (hm.comp pairRadius_measurable)
  have eq (x : SphereAmbient I W) : f ((J x).1,‖(J x).2‖)=B x*h ‖x‖ := by
    unfold f B J pairProjection normalizedCoords
    rw [←norm_as_pairRadius x]
  let H := fun p : (I→ℝ)×W => f (p.1,‖p.2‖)
  have Hm : Measurable H := fm.comp (measurable_fst.prodMk (measurable_norm.comp measurable_snd))
  have HAm : Measurable (fun p : (I→ℝ)×W => A p.2 * H p) := (Am.comp measurable_snd).mul Hm
  have left := jm.lintegral_comp HAm
  have right := jm.lintegral_comp Hm
  change (∫⁻ x, A' x * f ((J x).1,‖(J x).2‖) ∂μ) = _ at left
  change (∫⁻ x, f ((J x).1,‖(J x).2‖) ∂μ) = _ at right
  simp_rw [eq,←mul_assoc] at left
  simp_rw [eq] at right
  have fact := residual_angular_product (I:=I) f fm A Am Ah
  change (∫⁻ p, A p.2*H p) = D * ∫⁻ p,H p at fact
  rw [←left,←right,wrap B mm bi,
    wrap (fun x => A' x*B x) (ma.mul mm) (fun x b bp => by rw [ai x b bp,bi x b bp])] at fact
  have ht (u : UnitSphere (SphereAmbient I W)) : B u.val=g (ofLp (ofLp u.val).1) :=
    congrArg g (normalizedCoords_sphere u)
  simp_rw [ht] at fact
  change _ = D * _
  unfold uniformSphere
  rw [lintegral_smul_measure,lintegral_smul_measure,smul_eq_mul,smul_eq_mul]
  rw [show (∫⁻ u : UnitSphere (SphereAmbient I W), A (ofLp u.val).2*g (ofLp (ofLp u.val).1)
      ∂μ.toSphere) = _ from fact]
  ac_rfl

#print axioms spherical_residual_angular_independence
end RobustFolkman.GeometricGap
