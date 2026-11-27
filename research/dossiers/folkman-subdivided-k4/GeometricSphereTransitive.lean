import GeometricRotations
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

namespace RobustFolkman
open MeasureTheory Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem equal_norm_isometry (a b : E) (hn : ‖a‖=‖b‖) :
    ∃ e : E ≃ₗᵢ[ℝ] E, e a=b := by
  by_cases eq : a=b
  · exact ⟨LinearIsometryEquiv.refl ℝ E,eq⟩
  let u := a-b
  let K : Submodule ℝ E := Submodule.span ℝ {u}
  refine ⟨Kᗮ.reflection,?_⟩
  have nu : ‖u‖≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr eq)
  have p : ‖u‖^2=2*⟪u,a⟫_ℝ := by
    rw [←real_inner_self_eq_norm_sq]
    dsimp [u]
    rw [inner_sub_left,inner_sub_right,inner_sub_right,inner_sub_left]
    have xx : ⟪a,a⟫_ℝ=⟪b,b⟫_ℝ := by simp only [real_inner_self_eq_norm_sq,hn]
    have xy : ⟪a,b⟫_ℝ=⟪b,a⟫_ℝ := real_inner_comm _ _
    linarith only [xx,xy]
  have q : 2*(⟪u,a⟫_ℝ/‖u‖^2)=1 := by
    field_simp
    linarith only [p]
  rw [Submodule.reflection_orthogonal_apply]
  change -((ℝ ∙ u).reflection a)=b
  rw [Submodule.reflection_singleton_apply]
  rw [RCLike.ofReal_real_eq_id,id_eq]
  have h : 2 • (⟪u,a⟫_ℝ/‖u‖^2) • u=u := by
    rw [two_smul, ←add_smul]
    have r : ⟪u,a⟫_ℝ/‖u‖^2 + ⟪u,a⟫_ℝ/‖u‖^2=1 := by linarith only [q]
    rw [r,one_smul]
  rw [h]
  dsimp [u]
  abel

/-- The measure-preserving linear isometries act transitively on the
unit sphere with normalized Haar measure. -/
theorem uniformSphere_transitive (a b : UnitSphere E) :
    ∃ e : E ≃ₗᵢ[ℝ] E, sphereRotation e a=b ∧
      MeasurePreserving (sphereRotation e) (uniformSphere (volume : Measure E))
        (uniformSphere (volume : Measure E)) := by
  have n (a : UnitSphere E) : ‖(a:E)‖=1 := by simpa using a.property
  obtain ⟨e,he⟩ := equal_norm_isometry (a:E) (b:E) ((n a).trans (n b).symm)
  exact ⟨e,Subtype.ext he,sphereRotation_volume e⟩

#print axioms uniformSphere_transitive
end RobustFolkman
