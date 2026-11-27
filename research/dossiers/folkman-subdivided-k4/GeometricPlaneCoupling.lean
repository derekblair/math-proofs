import GeometricPlaneReflection

namespace RobustFolkman.GeometricGap
open Submodule
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_tangent_unit (dim : 2≤Module.finrank ℝ E) (u : E) (u1 : ‖u‖=1) :
    ∃ v : E, ‖v‖=1 ∧ ⟪u,v⟫_ℝ=0 := by
  let K := ℝ ∙ u
  let n := Module.finrank ℝ E-1
  letI : Fact (Module.finrank ℝ E=n+1) := ⟨by dsimp [n]; omega⟩
  have d : Module.finrank ℝ Kᗮ=n :=
    finrank_orthogonal_span_singleton (n:=n) (norm_ne_zero_iff.mp (by simp [u1]))
  letI : Nontrivial Kᗮ := Module.nontrivial_of_finrank_pos (R:=ℝ) (by rw [d]; dsimp [n]; omega)
  obtain ⟨v,hv⟩ := (NormedSpace.sphere_nonempty (E:=Kᗮ) (x:=0) (r:=1)).mpr zero_le_one
  exact ⟨v.val,by simpa using hv,Submodule.mem_orthogonal_singleton_iff_inner_right.mp v.property⟩

theorem unit_difference_reflects (x y : E) (x1 : ‖x‖=1) (y1 : ‖y‖=1) (ne : x≠y) :
    let n := ‖x-y‖⁻¹ • (x-y)
    ‖n‖=1 ∧ normalReflection n x = y := by
  intro n
  let z := x-y
  have zp : 0<‖z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr ne)
  have n1 : ‖n‖=1 := by
    change ‖‖z‖⁻¹ • z‖=1
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr zp),inv_mul_cancel₀ zp.ne']
  refine ⟨n1,?_⟩
  rw [normalReflection_unit_apply n x n1]
  have eq : ‖z‖^2=2*⟪z,x⟫_ℝ := by
    change ‖x-y‖^2=2*⟪x-y,x⟫_ℝ
    rw [norm_sub_sq_real,inner_sub_left,real_inner_self_eq_norm_sq,real_inner_comm x y,x1,y1]
    ring
  have nEq : n=‖z‖⁻¹ • z := rfl
  rw [nEq,real_inner_smul_left,smul_smul]
  have ee : 2*(‖z‖⁻¹*⟪z,x⟫_ℝ)*‖z‖⁻¹=1 := by
    field_simp [zp.ne']
    linarith only [eq]
  rw [ee,one_smul]
  dsimp [z]
  abel

theorem decompose_unit_in_plane (dim : 2≤Module.finrank ℝ E) (u n : E)
    (u1 : ‖u‖=1) (n1 : ‖n‖=1) :
    ∃ v : E, ∃ c d : ℝ, ‖v‖=1 ∧ ⟪u,v⟫_ℝ=0 ∧
      n=c • u+d • v ∧ c^2+d^2=1 := by
  let c := ⟪u,n⟫_ℝ
  let w := n-c • u
  have uu : ⟪u,u⟫_ℝ=1 := by rw [real_inner_self_eq_norm_sq,u1,one_pow]
  have wH : ⟪u,w⟫_ℝ=0 := by
    dsimp [w]
    rw [inner_sub_right,real_inner_smul_right,uu,mul_one]
    exact sub_self _
  have sq (v : E) (d : ℝ) (v1 : ‖v‖=1) (uv : ⟪u,v⟫_ℝ=0) (eq : n=c • u+d • v) :
      c^2+d^2=1 := by
    have p : ‖n‖^2=c^2+d^2 := by
      rw [eq,norm_add_sq_real,norm_smul,norm_smul,real_inner_smul_left,real_inner_smul_right,
        Real.norm_eq_abs,Real.norm_eq_abs,u1,v1,mul_one,mul_one,sq_abs,sq_abs,uv]
      ring
    nlinarith only [p,n1]
  by_cases z : w=0
  · obtain ⟨v,v1,uv⟩ := exists_tangent_unit dim u u1
    have eq : n=c • u+(0:ℝ) • v := by
      rw [zero_smul,add_zero]
      exact sub_eq_zero.mp z
    exact ⟨v,c,0,v1,uv,eq,sq v 0 v1 uv eq⟩
  · let d := ‖w‖
    let v := d⁻¹ • w
    have dp : 0<d := norm_pos_iff.mpr z
    have v1 : ‖v‖=1 := by
      dsimp [v]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr dp)]
      change d⁻¹*d=1
      exact inv_mul_cancel₀ dp.ne'
    have uv : ⟪u,v⟫_ℝ=0 := by dsimp [v]; rw [real_inner_smul_right,wH,mul_zero]
    have eq : n=c • u+d • v := by
      dsimp [v]
      rw [smul_smul,mul_inv_cancel₀ dp.ne',one_smul]
      dsimp [w]
      abel
    exact ⟨v,c,d,v1,uv,eq,sq v d v1 uv eq⟩

/-- For any two unit vectors in dimension at least two, a measure-
preserving plane isometry couples the two caps with an exact displacement
controlled by the projection onto the connecting plane. -/
theorem sphere_plane_coupling (dim : 2≤Module.finrank ℝ E) (x y : E) (x1 : ‖x‖=1) (y1 : ‖y‖=1) :
    ∃ (v : E) (R : E ≃ₗᵢ[ℝ] E), ‖v‖=1 ∧ ⟪x,v⟫_ℝ=0 ∧ R x=y ∧
      ∀ z : E, ‖R z-z‖^2=‖y-x‖^2*(⟪x,z⟫_ℝ^2+⟪v,z⟫_ℝ^2) := by
  by_cases e : x=y
  · subst y
    obtain ⟨v,v1,xv⟩ := exists_tangent_unit dim x x1
    exact ⟨v,LinearIsometryEquiv.refl ℝ E,v1,xv,rfl,fun z => by simp⟩
  let n := ‖x-y‖⁻¹ • (x-y)
  obtain ⟨n1,hn⟩ := unit_difference_reflects x y x1 y1 e
  obtain ⟨v,c,d,v1,xv,nd,cd⟩ := decompose_unit_in_plane dim x n x1 n1
  let R := (normalReflection v).trans (normalReflection n)
  have z : R x=y := by
    change normalReflection n (normalReflection v x)=y
    rw [normalReflection_unit_apply v x v1,real_inner_comm x v,xv,mul_zero,zero_smul,sub_zero]
    exact hn
  have form (w : E) : ‖R w-w‖^2=4*c^2*(⟪x,w⟫_ℝ^2+⟪v,w⟫_ℝ^2) :=
    plane_rotation_from_reflections x v n c d x1 v1 n1 xv nd cd w
  have h : ‖y-x‖^2=4*c^2 := by
    have f := form x
    rw [z,real_inner_self_eq_norm_sq,x1,real_inner_comm x v,xv] at f
    simpa using f
  exact ⟨v,R,v1,xv,z,fun w => (form w).trans (by rw [h])⟩

#print axioms sphere_plane_coupling
end RobustFolkman.GeometricGap
