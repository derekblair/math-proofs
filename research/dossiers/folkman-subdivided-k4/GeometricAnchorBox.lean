import GeometricLocalize

namespace RobustFolkman.GeometricGap
open Finset Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem localized_offdiag (M : Matrix I I ℝ) (psd : M.PosSemidef)
    (d0 : M.det≠0) (diag : ∀ i, M i i=1) (t : ℝ) (t0 : 0≤t)
    (lower : 1-729*t^2≤M.det) :
    ∀ i j, |M i j-(1 : Matrix I I ℝ) i j|≤27*t := by
  intro i j
  by_cases eq : i=j
  · subst j
    simpa [diag] using (mul_nonneg (by norm_num : (0:ℝ)≤27) t0)
  · rw [Matrix.one_apply_ne eq,sub_zero]
    have pv := det_pair_upper M psd d0 diag eq
    have sq : (M i j)^2≤(27*t)^2 := by nlinarith only [pv,lower]
    rw [←sq_abs (M i j)] at sq
    have qt : 0≤27*t := by positivity
    exact (sq_le_sq₀ (abs_nonneg (M i j)) qt).mp sq

theorem schur_small_concrete (A : Matrix I I ℝ) [Invertible A]
    (B : Matrix I (Fin 2) ℝ) (n : Fintype.card I≤6)
    (t : ℝ) (t0 : 0<t) (ts : t≤1/20000)
    (near : ∀ i j, |A i j-(1 : Matrix I I ℝ) i j|≤27*t)
    (bnear : ∀ i j, |B i j|≤27*t) (a b : Fin 2) :
    |(B.transpose*⅟A*B) a b|<t/2 := by
  have n6 : (Fintype.card I : ℝ)≤6 := by exact_mod_cast n
  have n0 : 0≤(Fintype.card I : ℝ) := by positivity
  have q0 : 0≤27*t := by positivity
  have m : (Fintype.card I : ℝ)*(27*t) ≤ 6*(27*t) :=
    mul_le_mul_of_nonneg_right n6 q0
  have k : 6*(27*t) < 1/2 := by linarith only [ts]
  have r : 0<1-(Fintype.card I : ℝ)*(27*t) := by linarith only [m,k]
  have inner : 27*t/(1-(Fintype.card I : ℝ)*(27*t))≤2*(27*t) := by
    apply (div_le_iff₀ r).mpr
    have k2 : 0≤1/2-(Fintype.card I : ℝ)*(27*t) := by linarith only [m,k]
    nlinarith only [mul_nonneg (show 0≤2*(27*t) by positivity) k2]
  have p := schur_prediction_bound A B (27*t) q0 r near bnear a b
  have big : (Fintype.card I : ℝ)*(27*t)*(27*t/(1-(Fintype.card I : ℝ)*(27*t))) ≤
      8748*t^2 := by
    calc
      _ ≤ (Fintype.card I : ℝ)*(27*t)*(2*(27*t)) :=
        mul_le_mul_of_nonneg_left inner (mul_nonneg n0 q0)
      _ ≤ 6*(27*t)*(2*(27*t)) := mul_le_mul_of_nonneg_right m (by positivity)
      _ = _ := by ring
  have margin : 8748*t^2<t/2 := by
    have q : 0<1/2-8748*t := by linarith only [ts]
    nlinarith only [mul_pos t0 q]
  exact p.trans_lt (big.trans_lt margin)

theorem anchorBlock_positive (A : Matrix I I ℝ) (sym : A.IsHermitian)
    (B : Matrix I (Fin 2) ℝ) (n : Fintype.card I≤6)
    (t s : ℝ) (t0 : 0<t) (ts : t≤1/20000)
    (near : ∀ i j, |A i j-(1 : Matrix I I ℝ) i j|≤27*t)
    (bnear : ∀ i j, |B i j|≤27*t) (h : |s|≤27*t) :
    (anchorBlock A B s).PosDef := by
  have ps : (setAnchor s).IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [setAnchor,Matrix.conjTranspose_apply]
  have ss : (anchorBlock A B s).IsHermitian := by
    unfold anchorBlock
    rw [←Matrix.conjTranspose_eq_transpose_of_trivial B]
    exact Matrix.IsHermitian.fromBlocks sym rfl ps
  have nc : (Fintype.card (I⊕Fin 2) : ℝ)≤8 := by
    simp only [Fintype.card_sum,Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat]
    have n6 : (Fintype.card I : ℝ)≤6 := by exact_mod_cast n
    linarith only [n6]
  apply near_identity_pd _ ss (27*t) (by positivity)
  · have q := mul_le_mul_of_nonneg_left nc (show 0≤27*t by positivity)
    linarith only [q,ts]
  · intro i j
    rcases i with i|i <;> rcases j with j|j
    · simpa [anchorBlock,Matrix.one_apply] using near i j
    · simpa [anchorBlock,Matrix.one_apply] using bnear i j
    · simpa [anchorBlock,Matrix.one_apply] using bnear j i
    · fin_cases i <;> fin_cases j <;> simp [anchorBlock,setAnchor,h,t0.le]

/-- At a constrained local optimum the correlation is clipped exactly
to the threshold. At a free optimum it is smaller than half of it. -/
theorem anchor_box_saturation (A : Matrix I I ℝ) (pd : A.PosDef)
    (B : Matrix I (Fin 2) ℝ) (n : Fintype.card I≤6)
    (t s : ℝ) (t0 : 0<t) (ts : t≤1/20000)
    (edge : Prop)
    (near : ∀ i j, |A i j-(1 : Matrix I I ℝ) i j|≤27*t)
    (bnear : ∀ i j, |B i j|≤27*t)
    (se : edge → t≤s)
    (best : ∀ v, (edge → t≤v) → (anchorBlock A B v).PosDef →
      (anchorBlock A B v).det≤(anchorBlock A B s).det) :
    (edge → s=t) ∧ (¬edge → |s|<t/2) := by
  let _ : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr pd.det_pos.ne')
  let W := B.transpose*⅟A*B
  let c := (W 0 1 + W 1 0)/2
  have w (a b : Fin 2) : |W a b|<t/2 := schur_small_concrete A B n t t0 ts near bnear a b
  have csmall : |c|<t/2 := by
    dsimp [c]
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    apply (div_lt_iff₀ (by norm_num : (0:ℝ)<2)).2
    exact (abs_add_le _ _).trans_lt (by linarith only [w 0 1,w 1 0])
  refine ⟨?_,?_⟩
  · intro e
    by_contra neq
    have st : t<s := (se e).lt_of_ne (Ne.symm neq)
    have ft : |t|≤27*t := by rw [abs_of_pos t0]; linarith only [t0]
    have bp := best t (fun _ => le_rfl) (anchorBlock_positive A pd.isHermitian B n t t t0 ts near bnear ft)
    have l (a b : Fin 2) : W a b<t := (le_abs_self _).trans_lt (by linarith only [w a b,t0])
    exact (anchor_clip_strict A B pd.det_pos s t st (l 0 1) (l 1 0)).not_ge bp
  · intro no
    have ce : |c|≤27*t := by linarith only [csmall,t0]
    have bp := best c (fun h => False.elim (no h))
      (anchorBlock_positive A pd.isHermitian B n t c t0 ts near bnear ce)
    by_cases h : s=c
    · exact h.symm ▸ csmall
    · exact False.elim (((anchor_center_strict A B pd.det_pos s) h).not_ge bp)

#print axioms localized_offdiag
#print axioms anchor_box_saturation
end RobustFolkman.GeometricGap
