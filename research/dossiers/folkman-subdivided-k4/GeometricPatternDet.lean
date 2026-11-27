import GeometricForbidden

namespace RobustFolkman.GeometricGap
open Matrix

def edgeCon (i j : Fin 2) : Prop := i≠j
def triangleCon := pageEdges edgeCon (0:Fin 2) 1
def extCon := pageEdges subEdges (Sum.inl (Sum.inr (0:Fin 2)) : Five) (Sum.inr ())

theorem edgeCon_sym : ∀ i j, edgeCon i j ↔ edgeCon j i := fun _ _ => ne_comm
theorem triangleCon_sym : ∀ i j, triangleCon i j ↔ triangleCon j i := pageEdges_sym _ edgeCon_sym _ _
theorem extCon_sym : ∀ i j, extCon i j ↔ extCon j i := pageEdges_sym _ subEdges_sym _ _

def GramOptimal {I : Type*} [Fintype I] [DecidableEq I]
    (C : I→I→Prop) (t : ℝ) (M : Matrix I I ℝ) : Prop :=
  GramFeasible C t M ∧ ∀ A, GramFeasible C t A → A.det≤M.det

theorem edge_det_exact (t : ℝ) (t0 : 0<t) (ts : t≤1/20000)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (mo : GramOptimal edgeCon t M) :
    M.det=1-t^2 := by
  have e01 := (all_pairs_saturation edgeCon edgeCon_sym (by decide) t t0 ts M mo.1 mo.2
    0 1 (by decide)).1 (by simp [edgeCon])
  have e10 := (all_pairs_saturation edgeCon edgeCon_sym (by decide) t t0 ts M mo.1 mo.2
    1 0 (by decide)).1 (by simp [edgeCon])
  rw [Matrix.det_fin_two,mo.1.2.1,mo.1.2.1,e01,e10]
  ring

theorem diamond_det_exact (t : ℝ) (t0 : 0<t) (ts : t≤1/20000)
    (M : Matrix Four Four ℝ) (mo : GramOptimal diamondEdges t M) :
    M.det=(1-t^2)*pageFactor t t^2 := by
  classical
  have t1 : t<1 := by linarith only [ts]
  have sat := all_pairs_saturation diamondEdges diamond_sym (by decide) t t0 ts M mo.1 mo.2
  have MA : M.submatrix Sum.inl Sum.inl=setAnchor t := by
    ext i j
    fin_cases i <;> fin_cases j
    · exact mo.1.2.1 _
    · exact (sat (.inl 0) (.inl 1) (by decide)).1 (by simp [diamondEdges])
    · exact (sat (.inl 1) (.inl 0) (by decide)).1 (by simp [diamondEdges])
    · exact mo.1.2.1 _
  have MB : M.submatrix Sum.inl Sum.inr=uniformB t := by
    ext i j
    exact (sat (.inl i) (.inr j) (by simp)).1 trivial
  have EQ := anchorBlock_eq M mo.1.1.isHermitian mo.1.2.1
  rw [MA,MB] at EQ
  have hi : M.det≤(1-t^2)*pageFactor t t^2 := EQ ▸ diamondGram_upper t _ t0 t1
  let g := 2*t^2/(1+t)
  have g0 : 0≤g := by dsimp [g]; positivity
  have gt : g<t := centered_less t0 (by linarith only [ts])
  have Aherm : (setAnchor t).IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [setAnchor,Matrix.conjTranspose_apply]
  have An (i j : Fin 2) : |setAnchor t i j-(1 : Matrix (Fin 2) (Fin 2) ℝ) i j|≤27*t := by
    fin_cases i <;> fin_cases j <;> simp [setAnchor,abs_of_nonneg t0.le] <;> linarith only [t0]
  have Bn (i j : Fin 2) : |uniformB t i j|≤27*t := by
    simp [uniformB,abs_of_nonneg t0.le]
    linarith only [t0]
  have g27 : |g|≤27*t := by rw [abs_of_nonneg g0]; linarith only [gt,t0]
  have pd : (diamondGram t g).PosDef :=
    anchorBlock_positive (setAnchor t) Aherm (uniformB t) (by decide) t g t0 ts An Bn g27
  have ff : GramFeasible diamondEdges t (diamondGram t g) := by
    refine ⟨pd.posSemidef,?_,?_⟩
    · intro i
      rcases i with i|i <;> fin_cases i <;> rfl
    · intro i j h
      rcases i with i|i <;> rcases j with j|j
      · fin_cases i <;> fin_cases j
        · exact False.elim (h rfl)
        · exact le_rfl
        · exact le_rfl
        · exact False.elim (h rfl)
      · exact le_rfl
      · exact le_rfl
      · exact False.elim h
  have lo := mo.2 _ ff
  rw [diamondGram_det t g t0 t1] at lo
  dsimp [g] at lo
  simp only [sub_self,zero_pow (by decide : (2:ℕ)≠0),sub_zero] at lo
  exact le_antisymm hi lo

/-- Exact pattern comparisons for all five actual constrained maxima. -/
theorem exact_pattern_determinants (t : ℝ) (t0 : 0<t) (ts : t≤1/20000)
    (E : Matrix (Fin 2) (Fin 2) ℝ)
    (T : Matrix (Fin 2⊕Unit) (Fin 2⊕Unit) ℝ)
    (D : Matrix Four Four ℝ) (H : Matrix Five Five ℝ)
    (J : Matrix (Five⊕Unit) (Five⊕Unit) ℝ)
    (e : GramOptimal edgeCon t E) (tr : GramOptimal triangleCon t T)
    (d : GramOptimal diamondEdges t D) (h : GramOptimal subEdges t H)
    (j : GramOptimal extCon t J) :
    E.det=1-t^2 ∧ T.det=E.det*pageFactor t t ∧ D.det=E.det*pageFactor t t^2 ∧
      H.det<E.det*pageFactor t t^3 ∧ J.det=H.det*pageFactor t t := by
  have Ee := edge_det_exact t t0 ts E e
  refine ⟨Ee,?_,?_,?_,?_⟩
  · exact page_opt_factor edgeCon edgeCon_sym (by decide) 0 1 (by decide) (by simp [edgeCon])
      t t0 ts E T e.1 e.2 tr.1 tr.2
  · rw [Ee]
    exact diamond_det_exact t t0 ts D d
  · rw [Ee]
    exact forbidden_opt_strict t t0 ts H h.1 h.2
  · exact page_opt_factor subEdges subEdges_sym (by decide) (.inl (.inr 0)) (.inr ())
      (by decide) (Or.inl rfl) t t0 ts H J h.1 h.2 j.1 j.2

#print axioms exact_pattern_determinants
end RobustFolkman.GeometricGap
