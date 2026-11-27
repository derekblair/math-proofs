import GeometricPlaneCoupling
import GeometricRootTransport
import GeometricRootCap

namespace RobustFolkman.GeometricGap
open MeasureTheory Set WithLp
open scoped ENNReal InnerProductSpace

theorem conditional_transport {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (f : S → T) {σ : Measure S} {τ : Measure T} (hp : MeasurePreserving f σ τ)
    (B : Set T) (bm : MeasurableSet B) :
    MeasurePreserving f (condOn σ (f ⁻¹' B)) (condOn τ B) := by
  refine ⟨hp.measurable,?_⟩
  unfold condOn
  rw [Measure.map_smul _ hp.measurable.aemeasurable,
    ←Measure.restrict_map hp.measurable bm,hp.map_eq,hp.measure_preimage bm.nullMeasurableSet]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- In every unit tangent direction, the conditional spherical cap has
second moment at most the uniform tangent-sphere moment. -/
theorem cap_tangent_second_moment (dim : 3≤Module.finrank ℝ E) (t : ℝ)
    (t0 : -1<t) (t1 : t<1) (a v : UnitSphere E) (av : ⟪a.val,v.val⟫_ℝ=0) :
    (∫ z : UnitSphere E, (⟪v.val,z.val⟫_ℝ)^2
      ∂condOn (uniformSphere (volume : Measure E)) (capPoints t a)) ≤
      1/((Module.finrank ℝ E:ℝ)-1) := by
  obtain ⟨K,e,he,hD⟩ := root_shell_isometry a
  let W := ↥Kᗮ
  let m := Module.finrank ℝ W-2
  have wD : Module.finrank ℝ W=m+2 := by dsimp [W,m] at *; omega
  letI : Nontrivial W := Module.nontrivial_of_finrank_pos (R:=ℝ) (by omega)
  letI : Nontrivial (SphereAmbient (Fin 1) W) := e.injective.nontrivial
  let f := sphereTransport e
  let σ := uniformSphere (volume : Measure E)
  let τ := uniformSphere (volume : Measure (SphereAmbient (Fin 1) W))
  let υ := uniformSphere (volume : Measure W)
  let H : Set (Fin 1→ℝ) := {u | t≤u 0}
  have Hm : MeasurableSet H := measurableSet_le measurable_const (measurable_pi_apply 0)
  let B := sphereCoord (I:=Fin 1) (W:=W) ⁻¹' H
  have Bm : MeasurableSet B := sphereCoord_measurable Hm
  have pre : f ⁻¹' B = capPoints t a := by
    ext z
    exact (show (t≤sphereHeight (f z)) ↔ t≤⟪a.val,z.val⟫_ℝ by rw [he z])
  have fV : MeasurePreserving f σ τ := sphereTransport_volume e
  have cond := conditional_transport f fV B Bm
  rw [pre] at cond
  have ns : σ (capPoints t a)≠0 := (capPoints_both_positive t t0 t1 a).1.ne'
  have nt : τ B≠0 := by
    rw [←fV.measure_preimage Bm.nullMeasurableSet,pre]
    exact ns
  letI : IsProbabilityMeasure τ := uniformSphere_isProbability _
  let τ' := condOn τ B
  letI : IsProbabilityMeasure τ' := condOn_probability τ B nt (measure_ne_top τ B)
  have rr : MeasurePreserving (sphereResidual (I:=Fin 1) (W:=W)) τ' υ :=
    conditioned_residual_uniform m wD H Hm nt
  let b := f v
  let w := (ofLp b.val).2
  have bz : sphereHeight b=0 := (he v).trans av
  have b1 : ‖w‖=1 := by
    have h := sphere_residual_radius b
    rw [bz,zero_pow (by decide),sub_zero] at h
    change ‖w‖^2=1 at h
    by_contra ne
    have r : (‖w‖-1)*(‖w‖+1)=0 := by nlinarith only [h]
    exact (mul_ne_zero (sub_ne_zero.mpr ne) (by positivity)) r
  let vW : UnitSphere W := ⟨w,by change dist w (0:W)=1; rw [dist_zero_right,b1]⟩
  let g := fun z : UnitSphere (SphereAmbient (Fin 1) W) => (⟪w,(ofLp z.val).2⟫_ℝ)^2
  let G := fun z : UnitSphere W => (⟪w,z.val⟫_ℝ)^2
  have gg (z : UnitSphere E) : g (f z)=(⟪v.val,z.val⟫_ℝ)^2 := by
    have q := e.inner_map_map v.val z.val
    change ⟪b.val,(f z).val⟫_ℝ=⟪v.val,z.val⟫_ℝ at q
    rw [WithLp.prod_inner_apply] at q
    change ⟪(ofLp b.val).1,(ofLp (f z).val).1⟫_ℝ+⟪w,(ofLp (f z).val).2⟫_ℝ=_ at q
    rw [PiLp.inner_apply,Fin.sum_univ_one] at q
    change ⟪sphereHeight b,sphereHeight (f z)⟫_ℝ+_=_ at q
    rw [bz,inner_zero_left,zero_add] at q
    exact congrArg (fun r : ℝ => r^2) q
  have ag := cond.integral_comp' g
  simp_rw [gg] at ag
  rw [ag]
  letI : IsProbabilityMeasure υ := uniformSphere_isProbability _
  have GI : Integrable G υ := sphere_inner_square_integrable vW υ
  have GG : (∫ z, G (sphereResidual z) ∂τ')=∫ y, G y ∂υ := by
    rw [←rr.map_eq,integral_map rr.aemeasurable (by rw [rr.map_eq]; exact GI.aestronglyMeasurable)]
  have bd : (∫ z, g z ∂τ')≤∫ z, G (sphereResidual z) ∂τ' := by
    apply integral_mono_of_nonneg
    · exact ae_of_all _ (fun _ => sq_nonneg _)
    · exact rr.integrable_comp_of_integrable GI
    · apply ae_of_all
      intro z
      let a' := (ofLp z.val).2
      have r := sphere_residual_radius z
      change ‖a'‖^2=1-(sphereHeight z)^2 at r
      by_cases a0 : a'=0
      · change (⟪w,a'⟫_ℝ)^2≤_
        rw [a0,inner_zero_right]
        simpa [G] using sq_nonneg ⟪w,(sphereResidual z).val⟫_ℝ
      · have h := residualDirection_rescale a' a0
        have e : ⟪w,a'⟫_ℝ=‖a'‖*⟪w,(sphereResidual z).val⟫_ℝ := by
          nth_rw 1 [←h]
          exact real_inner_smul_right _ _ _
        change (⟪w,a'⟫_ℝ)^2≤ _
        rw [e,mul_pow]
        exact mul_le_of_le_one_left (sq_nonneg _) (by nlinarith only [r,sq_nonneg (sphereHeight z)])
  rw [GG] at bd
  refine bd.trans_eq ?_
  have m := sphere_inner_square_mean vW
  convert m using 1
  congr 1
  have d : (Module.finrank ℝ E:ℝ)=1+(Module.finrank ℝ W:ℝ) := by exact_mod_cast hD
  linarith only [d]

#print axioms cap_tangent_second_moment
end RobustFolkman.GeometricGap
