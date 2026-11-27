import GeometricPage
import GeometricExactScalar

namespace RobustFolkman.GeometricGap
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

def pageEdges (C : I→I→Prop) (a b : I) : (I⊕Unit)→(I⊕Unit)→Prop
  | .inl i, .inl j => C i j
  | .inl i, .inr _ => i=a ∨ i=b
  | .inr _, .inl j => j=a ∨ j=b
  | .inr _, .inr _ => False

theorem pageEdges_sym (C : I→I→Prop) (h : ∀ i j, C i j ↔ C j i) (a b : I) :
    ∀ i j, pageEdges C a b i j ↔ pageEdges C a b j i := by
  intro i j
  rcases i with i|i <;> rcases j with j|j
  · exact h i j
  · rfl
  · rfl
  · rfl

theorem pageBorder_repr (M : Matrix (I⊕Unit) (I⊕Unit) ℝ)
    (sym : M.IsHermitian) (diag : M (.inr ()) (.inr ())=1) :
    M = pageBorder (M.submatrix Sum.inl Sum.inl) (fun i => M (.inl i) (.inr ())) := by
  ext i j
  rcases i with i|i <;> rcases j with j|j
  · rfl
  · cases j
    rfl
  · cases i
    change M (.inr ()) (.inl j)=star (M (.inl j) (.inr ()))
    exact (congrFun (congrFun sym.eq (.inr ())) (.inl j)).symm
  · cases i
    cases j
    simpa [pageBorder] using diag

theorem pageBorder_feasible (C : I→I→Prop) (a b : I) (t : ℝ) (A : Matrix I I ℝ) (c : I→ℝ)
    (f : GramFeasible C t A) (ca : t≤c a) (cb : t≤c b)
    (p : (pageBorder A c).PosSemidef) :
    GramFeasible (pageEdges C a b) t (pageBorder A c) := by
  refine ⟨p,?_,?_⟩
  · intro i
    rcases i with i|i
    · exact f.2.1 i
    · cases i
      simp [pageBorder]
  · intro i j h
    rcases i with i|i <;> rcases j with j|j
    · exact f.2.2 i j h
    · rcases h with rfl|rfl
      · exact ca
      · exact cb
    · rcases h with rfl|rfl
      · simpa [pageBorder,pageCol,Matrix.conjTranspose_apply] using ca
      · simpa [pageBorder,pageCol,Matrix.conjTranspose_apply] using cb
    · exact False.elim h

/-- A new page on an old constrained edge multiplies the maximal
correlation determinant by exactly the universal page factor. -/
theorem page_opt_factor (C : I→I→Prop) (sym : ∀ i j, C i j ↔ C j i)
    (n : Fintype.card (I⊕Unit)≤6) (a b : I) (ab : a≠b) (edge : C a b)
    (t : ℝ) (t0 : 0<t) (ts : t≤1/20000)
    (A : Matrix I I ℝ) (M : Matrix (I⊕Unit) (I⊕Unit) ℝ)
    (af : GramFeasible C t A) (am : ∀ N, GramFeasible C t N → N.det≤A.det)
    (mf : GramFeasible (pageEdges C a b) t M)
    (mm : ∀ N, GramFeasible (pageEdges C a b) t N → N.det≤M.det) :
    M.det=A.det*pageFactor t t := by
  classical
  have oldn : Fintype.card I≤6 := (Fintype.card_le_of_injective _ Sum.inl_injective).trans n
  have Apos := (optimum_is_localized C sym oldn t t0 ts A af am).1
  have Mpos := (optimum_is_localized (pageEdges C a b) (pageEdges_sym C sym a b)
    n t t0 ts M mf mm).1
  have ae : A a b=t := (all_pairs_saturation C sym oldn t t0 ts A af am a b ab).1 edge
  have me : M (.inl a) (.inl b)=t :=
    (all_pairs_saturation (pageEdges C a b) (pageEdges_sym C sym a b) n t t0 ts M mf mm
      (.inl a) (.inl b) (fun h => ab (Sum.inl.inj h))).1 edge
  have t1 : 0<1+t := by positivity
  have ff : 0≤pageFactor t t := by
    have ht : t≤1/2 := by linarith only [ts]
    have k := centered_less t0 ht
    unfold pageFactor
    linarith only [k,ts]
  have low : A.det*pageFactor t t≤M.det := by
    obtain ⟨c,ca,cb,cp,ce⟩ :=
      (page_achieves_exact A Apos a b (af.2.1 _) (af.2.1 _) t t ae t1 t0.le ff).2
    exact ce.symm ▸ mm _ (pageBorder_feasible C a b t A c af ca.ge cb.ge cp)
  have up : M.det≤A.det*pageFactor t t := by
    let D := M.submatrix Sum.inl Sum.inl
    let c : I→ℝ := fun i => M (.inl i) (.inr ())
    have dp : D.PosDef := Mpos.submatrix Sum.inl_injective
    have df : GramFeasible C t D := feasible_submatrix (pageEdges C a b) t M Sum.inl mf
    have dem := (page_achieves_exact D dp a b (df.2.1 _) (df.2.1 _) t t me t1 t0.le ff).1
      c (mf.2.2 _ _ (Or.inl rfl)) (mf.2.2 _ _ (Or.inr rfl))
    have rb : M=pageBorder D c := pageBorder_repr M mf.1.isHermitian (mf.2.1 _)
    rw [rb]
    exact dem.trans (mul_le_mul_of_nonneg_right (am D df) ff)
  exact le_antisymm up low

#print axioms page_opt_factor
end RobustFolkman.GeometricGap
