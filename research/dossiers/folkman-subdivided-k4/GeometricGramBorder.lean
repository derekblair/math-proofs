import GeometricGramConditional

namespace RobustFolkman.GeometricGap
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem gram_border_det (A : Matrix I I ℝ) (h : IsUnit A.det) (y : I→ℝ) :
    (pageBorder A y).det=A.det*(1-anchorQuad A y) := by
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A h
  rw [pageBorder,Matrix.det_fromBlocks₁₁,Matrix.det_unique
    (1-(pageCol y)ᴴ*⅟A*(pageCol y))]
  congr 1
  rw [Matrix.sub_apply,Matrix.one_apply_eq]
  unfold anchorQuad
  rw [Matrix.invOf_eq_nonsing_inv,Matrix.mul_assoc]
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial,pageCol,
    Matrix.mulVec,dotProduct]

theorem gram_border_pd (A : Matrix I I ℝ) (h : A.PosDef) (y : I→ℝ) :
    (pageBorder A y).PosDef ↔ anchorQuad A y<1 := by
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr h.det_pos.ne')
  have ss : ((1 : Matrix Unit Unit ℝ)-(pageCol y)ᴴ*⅟A*(pageCol y)) () () =
      1-anchorQuad A y := by
    rw [Matrix.sub_apply,Matrix.one_apply_eq]
    unfold anchorQuad
    rw [Matrix.invOf_eq_nonsing_inv,Matrix.mul_assoc]
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial,pageCol,
      Matrix.mulVec,dotProduct]
  have hs : (pageBorder A y).PosSemidef ↔ 0≤1-anchorQuad A y := by
    rw [pageBorder,Matrix.PosDef.fromBlocks₁₁ _ _ h,scalar_psd]
    rw [← Matrix.invOf_eq_nonsing_inv,ss]
  have d := gram_border_det A (isUnit_iff_ne_zero.mpr h.det_pos.ne') y
  constructor
  · intro h'
    have p := h'.det_pos
    rw [d] at p
    exact sub_pos.mp ((mul_pos_iff_of_pos_left h.det_pos).mp p)
  · intro l
    have p := sub_pos.mpr l
    apply pd_of_psd_det _ (hs.mpr p.le)
    rw [d]
    exact (mul_pos h.det_pos p).ne'

#print axioms gram_border_det
#print axioms gram_border_pd
end RobustFolkman.GeometricGap
