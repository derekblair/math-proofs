import GeometricSphereIsotropy
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

namespace RobustFolkman.GeometricGap
open Submodule
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def normalReflection (u : E) : E ≃ₗᵢ[ℝ] E := (ℝ ∙ u)ᗮ.reflection

theorem normalReflection_unit_apply (u y : E) (u1 : ‖u‖=1) :
    normalReflection u y = y - (2*⟪u,y⟫_ℝ) • u := by
  unfold normalReflection
  rw [Submodule.reflection_orthogonal_apply,Submodule.reflection_singleton_apply]
  simp only [u1, RCLike.ofReal_real_eq_id,id_eq,one_pow,div_one]
  rw [two_smul,←add_smul,←two_mul,neg_sub]

/-- Two reflections in the same coordinate plane make a rotation with
a displacement exactly proportional to the squared projected length. -/
theorem plane_rotation_from_reflections (u v n : E) (c d : ℝ)
    (u1 : ‖u‖=1) (v1 : ‖v‖=1) (n1 : ‖n‖=1)
    (uv : ⟪u,v⟫_ℝ=0) (nv : n=c • u+d • v) (cd : c^2+d^2=1) (y : E) :
    let R := (normalReflection v).trans (normalReflection n)
    ‖R y-y‖^2=4*c^2*(⟪u,y⟫_ℝ^2+⟪v,y⟫_ℝ^2) := by
  intro R
  let a := ⟪u,y⟫_ℝ
  let b := ⟪v,y⟫_ℝ
  have vu : ⟪v,u⟫_ℝ=0 := (real_inner_comm u v).trans uv
  have vv : ⟪v,v⟫_ℝ=1 := by rw [real_inner_self_eq_norm_sq,v1,one_pow]
  have nd : ⟪v,n⟫_ℝ=d := by
    rw [nv,inner_add_right,real_inner_smul_right,real_inner_smul_right,vu,vv]
    ring
  have lin : ⟪n,normalReflection v y⟫_ℝ=c*a-d*b := by
    rw [normalReflection_unit_apply v y v1]
    rw [inner_sub_right,real_inner_smul_right,real_inner_comm v n,nd]
    nth_rw 1 [nv]
    rw [inner_add_left,real_inner_smul_left,real_inner_smul_left]
    dsimp [a,b]
    ring
  have e : R y-y = (-2*b) • v + (-2*(c*a-d*b)) • n := by
    change (normalReflection n) (normalReflection v y)-y=_
    rw [normalReflection_unit_apply n _ n1,lin,normalReflection_unit_apply v y v1]
    dsimp [b]
    simp only [neg_mul,neg_smul]
    abel
  have h (z : ℝ) (w : E) (w1 : ‖w‖=1) : ‖z • w‖^2=z^2 := by
    rw [norm_smul,Real.norm_eq_abs,w1,mul_one,sq_abs]
  rw [e,norm_add_sq_real,h _ _ v1,h _ _ n1,
    real_inner_smul_left,real_inner_smul_right,nd]
  change _=4*c^2*(a^2+b^2)
  ring_nf
  have h1 := congrArg (fun k : ℝ => 4*b^2*k) cd
  nlinarith only [h1]

#print axioms plane_rotation_from_reflections
end RobustFolkman.GeometricGap
