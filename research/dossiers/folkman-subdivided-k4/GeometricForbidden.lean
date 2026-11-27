import GeometricDiamond

namespace RobustFolkman.GeometricGap
open Matrix
abbrev Five := Four ⊕ Unit

def diamondEdges : Four→Four→Prop
  | .inl i,.inl j => i≠j
  | .inl _,.inr _ => True
  | .inr _,.inl _ => True
  | .inr _,.inr _ => False

theorem diamond_sym : ∀ i j, diamondEdges i j ↔ diamondEdges j i := by
  intro i j
  rcases i with i|i <;> rcases j with j|j
  · exact ne_comm
  · rfl
  · rfl
  · rfl

def subEdges : Five→Five→Prop := pageEdges diamondEdges (.inr 0) (.inr 1)

theorem subEdges_sym : ∀ i j, subEdges i j ↔ subEdges j i :=
  pageEdges_sym diamondEdges diamond_sym _ _

/-- The actual constrained determinant maximum for the forbidden graph
has a strict quantitative gap relative to the three-page book. -/
theorem forbidden_opt_det_upper (t : ℝ) (t0 : 0<t) (ts : t≤1/20000)
    (M : Matrix Five Five ℝ)
    (mf : GramFeasible subEdges t M)
    (mm : ∀ N, GramFeasible subEdges t N → N.det≤M.det) :
    M.det≤(1-t^2)*pageFactor t t^2*pageFactor t (t/2) := by
  classical
  have cn : Fintype.card Five≤6 := by decide
  have sat := all_pairs_saturation subEdges subEdges_sym cn t t0 ts M mf mm
  let D := M.submatrix Sum.inl Sum.inl
  let u : Four := .inr 0
  let v : Four := .inr 1
  let r := D u v
  have ru : |r|<t/2 := (sat (.inl u) (.inl v) (by decide)).2 (by simp [subEdges,pageEdges,diamondEdges,u,v])
  have Rlo : -1<r := by
    have h := (abs_lt.mp ru).1
    linarith only [h,ts]
  have Rhi : r<t/2 := (abs_lt.mp ru).2
  have Dpos : D.PosDef :=
    (optimum_is_localized subEdges subEdges_sym cn t t0 ts M mf mm).1.submatrix Sum.inl_injective
  have dx : D.submatrix Sum.inl Sum.inl=setAnchor t := by
    ext i j
    fin_cases i <;> fin_cases j
    · exact mf.2.1 _
    · exact (sat (.inl (.inl 0)) (.inl (.inl 1)) (by decide)).1 (by simp [subEdges,pageEdges,diamondEdges])
    · exact (sat (.inl (.inl 1)) (.inl (.inl 0)) (by decide)).1 (by simp [subEdges,pageEdges,diamondEdges])
    · exact mf.2.1 _
  have db : D.submatrix Sum.inl Sum.inr=uniformB t := by
    ext i j
    exact (sat (.inl (.inl i)) (.inl (.inr j)) (by simp)).1 (by trivial)
  have eq : D=diamondGram t r := by
    have e := anchorBlock_eq D Dpos.isHermitian (fun i => mf.2.1 (.inl i))
    rw [dx,db] at e
    exact e.symm
  have posF : 0≤pageFactor t r := by
    unfold pageFactor
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (by linarith only [Rlo] : 0<1+r)).mpr
    have hpos := (abs_lt.mp ru).1
    have ht2 : t^2≤(1/2:ℝ)^2 := (sq_le_sq₀ t0.le (by norm_num)).mpr (by linarith only [ts])
    nlinarith only [ht2,hpos,ts]
  let c : Four → ℝ := fun i => M (.inl i) (.inr ())
  have bound := (page_achieves_exact D Dpos u v (mf.2.1 _) (mf.2.1 _)
    r t rfl (by linarith only [Rlo]) t0.le posF).1 c
    (mf.2.2 _ _ (Or.inl rfl)) (mf.2.2 _ _ (Or.inr rfl))
  have rb : M=pageBorder D c := pageBorder_repr M mf.1.isHermitian (mf.2.1 _)
  rw [←rb] at bound
  have up : D.det≤(1-t^2)*pageFactor t t^2 := by rw [eq]; exact diamondGram_upper t r t0 (by linarith only [ts])
  have less := (page_mono_strict t0 Rlo Rhi).le
  have c0 : 0≤(1-t^2)*pageFactor t t^2 := up.trans' Dpos.det_pos.le
  exact bound.trans ((mul_le_mul_of_nonneg_right up posF).trans (mul_le_mul_of_nonneg_left less c0))


theorem forbidden_opt_strict (t : ℝ) (t0 : 0<t) (ts : t≤1/20000)
    (M : Matrix Five Five ℝ)
    (mf : GramFeasible subEdges t M)
    (mm : ∀ N, GramFeasible subEdges t N → N.det≤M.det) :
    M.det<bThreeDet t := by
  have ht : t≤1/2 := by linarith only [ts]
  have p : 0<pageFactor t t := by
    have k := centered_less t0 ht
    unfold pageFactor
    linarith only [k,ht]
  have d : 0<1-t^2 := by
    have k := mul_pos (show 0<1-t by linarith only [ht]) (show 0<1+t by positivity)
    nlinarith only [k]
  have mono := page_mono_strict t0 (show -1<t/2 by linarith only [t0])
    (show t/2<t by linarith only [t0])
  have lt := mul_lt_mul_of_pos_left mono (mul_pos d (sq_pos_of_pos p))
  exact (forbidden_opt_det_upper t t0 ts M mf mm).trans_lt
    (by simpa [bThreeDet,pow_succ,mul_assoc] using lt)

#print axioms forbidden_opt_det_upper
#print axioms forbidden_opt_strict
end RobustFolkman.GeometricGap
