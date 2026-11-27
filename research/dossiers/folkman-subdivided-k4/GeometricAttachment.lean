import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace RobustFolkman.GeometricGap
variable {K E : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup E] [Module K E]

/-- Sharp quadratic cost of an additional vector with correlations at least t
to two old unit vectors of correlation r. This is the elementary Schur
complement optimization for attaching a triangle. -/
theorem attaching_triangle_quadratic
    (B : E →ₗ[K] E →ₗ[K] K) (sym : ∀ x y, B x y=B y x)
    (psd : ∀ x, 0≤B x x) (x y : E) (r t : K)
    (xx : B x x=1) (yy : B y y=1) (xy : B x y=r) (r0 : 0<1+r) (t0 : 0≤t) :
    (∀ z, t≤B x z → t≤B y z → 2*t^2/(1+r)≤B z z) ∧
    (∃ q, B x q=t ∧ B y q=t ∧ B q q=2*t^2/(1+r)) := by
  have rne : 1+r≠0 := ne_of_gt r0
  have yx : B y x=r := (sym _ _).trans xy
  let c := t/(1+r)
  let q := c • (x+y)
  have c0 : 0≤c := div_nonneg t0 r0.le
  have xq : B x q=t := by
    simp only [q,c,map_smul,map_add,smul_eq_mul,xx,xy]
    field_simp
  have yq : B y q=t := by
    simp only [q,c,map_smul,map_add,smul_eq_mul,yx,yy]
    field_simp
    ring
  have qform (z : E) : B q z=c*(B x z+B y z) := by
    simp only [q,map_smul,map_add,LinearMap.smul_apply,LinearMap.add_apply,smul_eq_mul]
  have qq : B q q=2*t^2/(1+r) := by
    rw [qform, xq, yq]
    unfold c
    field_simp
    ring
  refine ⟨?_,⟨q,xq,yq,qq⟩⟩
  intro z xz yz
  have qlow : B q q ≤ B q z := by
    have base := mul_le_mul_of_nonneg_left (add_le_add xz yz) c0
    rw [qform z]
    calc
      B q q = c*(t+t) := by rw [qform q,xq,yq]
      _ ≤ _ := base
  have h := psd (z-q)
  simp only [map_sub,LinearMap.sub_apply] at h
  rw [sym z q] at h
  linarith only [h,qlow,qq]

#print axioms attaching_triangle_quadratic
end RobustFolkman.GeometricGap
