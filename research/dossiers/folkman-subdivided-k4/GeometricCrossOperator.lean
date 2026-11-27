import GeometricGridOperator
import GeometricDecoupledNorm

namespace RobustFolkman.GeometricGap
open Matrix WithLp Finset
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {J : Type*} [Fintype J] [DecidableEq J]

abbrev LeftBlock (b : J→Bool) := {i : J // b i=false}
abbrev RightBlock (b : J→Bool) := {i : J // ¬ b i=false}

def crossRectangle (A : Matrix J J ℝ) (b : J→Bool) : Matrix (LeftBlock b) (RightBlock b) ℝ :=
  fun i j => A i.val j.val

/-- The symmetric off-block matrix has operator norm bounded by that
of the single rectangular block. The proof is via the Rayleigh form. -/
theorem cross_part_rectangular_norm (A : Matrix J J ℝ)
    (sym : ∀ i j, A i j=A j i) (b : J→Bool) :
    ‖crossPart A b‖ ≤ ‖crossRectangle A b‖ := by
  let F := crossRectangle A b
  let l := fun i : J => b i=false
  have hs : (crossPart A b).IsHermitian := by
    ext i j
    simp only [conjTranspose_apply,star_trivial,crossPart]
    rw [sym j i]
    by_cases h : b i=b j
    · simp [h]
    · simp [h,Ne.symm h]
  apply real_symmetric_matrix_norm_bound _ hs ‖F‖ (norm_nonneg _)
  intro v
  let x : EuclideanSpace ℝ (LeftBlock b) := toLp 2 (fun i => v i.val)
  let y : EuclideanSpace ℝ (RightBlock b) := toLp 2 (fun i => v i.val)
  have energy : ‖x‖^2+‖y‖^2=∑ i, (v i)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq x,EuclideanSpace.real_norm_sq_eq y]
    exact Fintype.sum_subtype_add_sum_subtype l (fun i => (v i)^2)
  let C := ∑ i : LeftBlock b, ∑ j : RightBlock b, A i.val j.val*(v i.val*v j.val)
  have eq : (∑ i : J, ∑ j : J, crossPart A b i j*(v i*v j)) = 2*C := by
    rw [←Fintype.sum_subtype_add_sum_subtype (fun i : J => b i=false)]
    have h₁ (i : LeftBlock b) : (∑ j : J, crossPart A b i.val j*(v i.val*v j)) =
        ∑ j : RightBlock b,A i.val j.val*(v i.val*v j.val) := by
      rw [←Fintype.sum_subtype_add_sum_subtype (fun i : J => b i=false)]
      have z (j : LeftBlock b) : crossPart A b i.val j.val=0 := by
        simp [crossPart,i.property,j.property]
      have w (j : RightBlock b) : crossPart A b i.val j.val=A i.val j.val := by
        simp [crossPart,i.property,Ne.symm j.property]
      simp only [z,w,zero_mul,Finset.sum_const_zero,zero_add,add_zero]
    have h₂ (i : RightBlock b) : (∑ j : J, crossPart A b i.val j*(v i.val*v j)) =
        ∑ j : LeftBlock b,A i.val j.val*(v i.val*v j.val) := by
      rw [←Fintype.sum_subtype_add_sum_subtype (fun i : J => b i=false)]
      have bi : b i.val=true := Bool.eq_true_of_not_eq_false i.property
      have z (j : RightBlock b) : crossPart A b i.val j.val=0 := by
        have bj : b j.val=true := Bool.eq_true_of_not_eq_false j.property
        simp [crossPart,bi,bj]
      have w (j : LeftBlock b) : crossPart A b i.val j.val=A i.val j.val := by
        simp [crossPart,bi,j.property]
      simp only [z,w,zero_mul,Finset.sum_const_zero,zero_add,add_zero]
    simp_rw [h₁,h₂]
    change C+(∑ i : RightBlock b, ∑ j : LeftBlock b,A i.val j.val*(v i.val*v j.val))=_
    have sw : (∑ i : RightBlock b, ∑ j : LeftBlock b,A i.val j.val*(v i.val*v j.val))=C := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [sym j.val i.val,mul_comm (v j.val) (v i.val)]
    rw [sw]
    ring
  let z := toLp 2 (F *ᵥ ofLp y)
  have bq : C=⟪x,z⟫_ℝ := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,x,z]
    simp only [dotProduct,Matrix.mulVec,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change A i.val j.val*(v i.val*v j.val)=(A i.val j.val*v j.val)*v i.val
    ring
  have uv : 2*(‖x‖*‖y‖)≤∑ i,(v i)^2 := by
    rw [←energy]
    nlinarith only [sq_nonneg (‖x‖-‖y‖)]
  have bv : ‖C‖≤‖F‖*(‖x‖*‖y‖) := by
    rw [bq,Real.norm_eq_abs]
    have h := abs_real_inner_le_norm x z
    have g : ‖z‖≤‖F‖*‖y‖ := Matrix.l2_opNorm_mulVec F y
    exact h.trans ((mul_le_mul_of_nonneg_left g (norm_nonneg _)).trans_eq (by ring))
  rw [eq,norm_mul,show ‖(2:ℝ)‖=2 by norm_num]
  calc
    _ ≤ 2*(‖F‖*(‖x‖*‖y‖)) := mul_le_mul_of_nonneg_left bv (by norm_num)
    _ = ‖F‖*(2*(‖x‖*‖y‖)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left uv (norm_nonneg _)

#print axioms cross_part_rectangular_norm
end RobustFolkman.GeometricGap
