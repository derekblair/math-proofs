import GeometricProbe

namespace RobustFolkman.GeometricGap
open Matrix
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [DecidableEq I] [DecidableEq J] in
theorem feasible_submatrix (C : J→J→Prop) (t : ℝ) (M : Matrix J J ℝ)
    (e : I→J) (h : GramFeasible C t M) :
    GramFeasible (fun i j => C (e i) (e j)) t (M.submatrix e e) :=
  ⟨h.1.submatrix _,fun i => h.2.1 _,fun i j h' => h.2.2 _ _ h'⟩

theorem anchorBlock_eq (M : Matrix (I⊕Fin 2) (I⊕Fin 2) ℝ)
    (sym : M.IsHermitian) (diag : ∀ i, M i i=1) :
    let A := M.submatrix Sum.inl Sum.inl
    let B := M.submatrix Sum.inl Sum.inr
    let s := M (.inr 0) (.inr 1)
    anchorBlock A B s=M := by
  intro A B s
  have H (i j : I⊕Fin 2) : M i j=M j i := by
    have h := congrFun (congrFun sym.eq i) j
    simpa [Matrix.conjTranspose_apply] using h.symm
  ext i j
  rcases i with i|i <;> rcases j with j|j
  · rfl
  · rfl
  · exact (H (.inl j) (.inr i))
  · fin_cases i <;> fin_cases j
    · exact (diag _).symm
    · rfl
    · exact H _ _
    · exact (diag _).symm

theorem block_anchor_saturation (C : (I⊕Fin 2)→(I⊕Fin 2)→Prop)
    (sym : ∀ i j, C i j ↔ C j i) (n : Fintype.card (I⊕Fin 2)≤6)
    (t : ℝ) (t0 : 0<t) (ts : t≤1/20000) (M : Matrix (I⊕Fin 2) (I⊕Fin 2) ℝ)
    (mf : GramFeasible C t M) (max : ∀ N, GramFeasible C t N → N.det≤M.det) :
    (C (.inr 0) (.inr 1) → M (.inr 0) (.inr 1)=t) ∧
    (¬C (.inr 0) (.inr 1) → |M (.inr 0) (.inr 1)|<t/2) := by
  classical
  let A := M.submatrix Sum.inl Sum.inl
  let B := M.submatrix Sum.inl Sum.inr
  let s := M (.inr 0) (.inr 1)
  let edge := C (.inr 0) (.inr 1)
  have EQ : anchorBlock A B s=M := anchorBlock_eq M mf.1.isHermitian mf.2.1
  obtain ⟨pd,close⟩ := optimum_is_localized C sym n t t0 ts M mf max
  have ap : A.PosDef := pd.submatrix Sum.inl_injective
  have nI : Fintype.card I≤6 := (Fintype.card_le_of_injective _ Sum.inl_injective).trans n
  have ca : ∀ i j, |A i j-(1 : Matrix I I ℝ) i j|≤27*t := by
    intro i j
    simpa [A,Matrix.submatrix_apply,Matrix.one_apply] using close (.inl i) (.inl j)
  have cb : ∀ i j, |B i j|≤27*t := by
    intro i j
    simpa [B,Matrix.submatrix_apply,Matrix.one_apply] using close (.inl i) (.inr j)
  apply anchor_box_saturation A ap B nI t s t0 ts edge ca cb (mf.2.2 _ _)
  intro v hv vp
  rw [EQ]
  apply max
  refine ⟨vp.posSemidef,?_,?_⟩
  · intro i
    rcases i with i|i
    · exact mf.2.1 _
    · fin_cases i <;> rfl
  · intro i j h
    have hsame : t≤1 := by linarith only [ts]
    rcases i with i|i <;> rcases j with j|j
    · exact mf.2.2 _ _ h
    · exact mf.2.2 _ _ h
    · have h' : t≤M (.inl j) (.inr i) := mf.2.2 _ _ ((sym _ _).mp h)
      exact h'
    · fin_cases i <;> fin_cases j
      · exact hsame
      · exact hv h
      · exact hv ((sym _ _).mp h)
      · exact hsame

/-- A determinant maximizer for a finite edge set on at most six vertices
saturates every edge and has strictly sub-half-threshold nonedges. -/
theorem all_pairs_saturation (C : J→J→Prop)
    (sym : ∀ i j, C i j ↔ C j i) (n : Fintype.card J≤6)
    (t : ℝ) (t0 : 0<t) (ts : t≤1/20000) (M : Matrix J J ℝ)
    (mf : GramFeasible C t M) (max : ∀ N, GramFeasible C t N → N.det≤M.det)
    (a b : J) (ab : a≠b) :
    (C a b → M a b=t) ∧ (¬C a b → |M a b|<t/2) := by
  classical
  let f : Fin 2→J := ![a,b]
  have fi : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f,Ne.symm ab]
  let P := Set.range f
  let U := ↥(Pᶜ : Set J)
  let _ : Fintype U := Fintype.ofFinite _
  let e : U⊕Fin 2 ≃ J :=
    ((Equiv.sumCongr (Equiv.refl U) (Equiv.ofInjective f fi)).trans
      (Equiv.sumComm U P)).trans (Equiv.sumCompl (fun x => x∈P))
  let Cp := fun i j => C (e i) (e j)
  let B := M.submatrix e e
  have cn : Fintype.card (U⊕Fin 2) ≤6 := (Fintype.card_congr e).le.trans n
  have bf : GramFeasible Cp t B := feasible_submatrix C t M e mf
  have mb (N : Matrix (U⊕Fin 2) (U⊕Fin 2) ℝ) (nf : GramFeasible Cp t N) :
      N.det≤B.det := by
    have nf' := feasible_submatrix Cp t N e.symm nf
    have nn : GramFeasible C t (N.submatrix e.symm e.symm) := by simpa [Cp] using nf'
    have hh := max _ nn
    rw [Matrix.det_submatrix_equiv_self] at hh
    exact (Matrix.det_submatrix_equiv_self e M).symm ▸ hh
  exact block_anchor_saturation Cp (fun i j => sym (e i) (e j)) cn t t0 ts B bf mb

#print axioms all_pairs_saturation
end RobustFolkman.GeometricGap
