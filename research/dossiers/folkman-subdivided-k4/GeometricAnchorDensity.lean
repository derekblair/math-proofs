import GeometricLinearProjection
import GeometricAnchorCoordinates

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory Set
open scoped ENNReal
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def anchorNorm (T : Matrix I I ℝ) (y : I→ℝ) : ℝ :=
  y ⬝ᵥ ((T*T.transpose)⁻¹ *ᵥ y)

def anchorEllipsoid (T : Matrix I I ℝ) : Set (I→ℝ) := {y | anchorNorm T y<1}

theorem anchor_image_ball (e : (I→ℝ) ≃L[ℝ] (I→ℝ))
    (T : Matrix I I ℝ) (d : IsUnit T.det) (E : ∀ x, e x=T*ᵥx) :
    e '' projectionBall = anchorEllipsoid T := by
  ext y
  have yn : anchorNorm T y=∑ i, (e.symm y) i^2 := by
    have h := anchor_inverse_norm T d (e.symm y)
    dsimp only at h
    rwa [← E, e.apply_symm_apply] at h
  constructor
  · rintro ⟨x,h,rfl⟩
    change anchorNorm T (e x)<1
    rw [yn,e.symm_apply_apply]
    exact h
  · intro h
    refine ⟨e.symm y,?_,e.apply_symm_apply y⟩
    change (∑ i, (e.symm y) i^2)<1
    rw [← yn]
    exact h

theorem anchor_density_integral (e : (I→ℝ) ≃L[ℝ] (I→ℝ))
    (T : Matrix I I ℝ) (d : IsUnit T.det) (E : ∀ x, e x=T*ᵥx)
    (m : ℕ) (f : (I→ℝ)→ℝ≥0∞) :
    (∫⁻ x in projectionBall, f (e x)*projectionFactor m x) =
    (∫⁻ y in anchorEllipsoid T, ENNReal.ofReal |e.symm.toContinuousLinearMap.det| *
      (f y*ENNReal.ofReal ((Real.sqrt (1-anchorNorm T y))^m))) := by
  rw [linear_projection_pushforward e projectionBall projectionBall_measurable f (projectionFactor m),
    anchor_image_ball e T d E]
  have ms : MeasurableSet (anchorEllipsoid T) := by
    rw [← anchor_image_ball e T d E]
    exact e.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr projectionBall_measurable
  apply setLIntegral_congr_fun ms
  intro y _
  dsimp only
  have s := anchor_inverse_norm T d (e.symm y)
  dsimp only at s
  rw [← E, e.apply_symm_apply] at s
  unfold projectionFactor anchorNorm
  rw [s]

theorem anchor_inverse_jacobian (e : (I→ℝ) ≃L[ℝ] (I→ℝ)) (T : Matrix I I ℝ)
    (E : ∀ x, e x=T*ᵥx) :
    |e.symm.toContinuousLinearMap.det| = (Real.sqrt (T*T.transpose).det)⁻¹ := by
  have eq : (e.toLinearEquiv : (I→ℝ) →ₗ[ℝ] (I→ℝ)) = Matrix.toLin' T :=
    LinearMap.ext fun x => E x
  have dn : T.det ≠ 0 := by
    rw [← LinearMap.det_toLin',← eq,← LinearEquiv.coe_det]
    exact Units.ne_zero _
  let D := LinearMap.det (e.toLinearEquiv.symm : (I→ℝ) →ₗ[ℝ] (I→ℝ))
  have prod : D*T.det=1 := by
    simpa only [D,eq,LinearMap.det_toLin'] using LinearEquiv.det_symm_mul_det e.toLinearEquiv
  have inv : D=T.det⁻¹ := by
    calc
      _ = D*(T.det*T.det⁻¹) := by rw [mul_inv_cancel₀ dn,mul_one]
      _ = _ := by rw [← mul_assoc,prod,one_mul]
  change |D|=_
  rw [inv,abs_inv,anchor_det_scale]

#print axioms anchor_inverse_jacobian
#print axioms anchor_density_integral
end RobustFolkman.GeometricGap
