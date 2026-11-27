import GeometricNearIdentity
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases

namespace RobustFolkman.GeometricGap
open Matrix
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem unit_border_det_le (M : Matrix (I⊕Unit) (I⊕Unit) ℝ)
    (pd : M.PosDef) (d : M (.inr ()) (.inr ())=1) :
    M.det ≤ (M.submatrix Sum.inl Sum.inl).det := by
  let A := M.submatrix Sum.inl Sum.inl
  let B : Matrix I Unit ℝ := fun i _ => M (.inl i) (.inr ())
  have hp : A.PosDef := pd.submatrix Sum.inl_injective
  have det0 := hp.det_pos
  let _ : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr det0.ne')
  have Z : M=Matrix.fromBlocks A B Bᴴ 1 := by
    ext i j
    rcases i with i|i <;> rcases j with j|j
    · rfl
    · rfl
    · cases i
      change M (.inr ()) (.inl j) = star (M (.inl j) (.inr ()))
      exact (congrFun (congrFun pd.isHermitian.eq (.inr ())) (.inl j)).symm
    · cases i
      cases j
      simpa using d
  have n : 0≤(Bᴴ*⅟A*B) () () := by
    rw [Matrix.invOf_eq_nonsing_inv]
    exact (hp.posSemidef.inv.conjTranspose_mul_mul_same B).diag_nonneg (i:=())
  rw [Z,Matrix.det_fromBlocks₁₁,Matrix.det_unique (1 - Bᴴ*⅟A*B)]
  have h : ((1 : Matrix Unit Unit ℝ)-Bᴴ*⅟A*B) () ()≤1 := by
    rw [Matrix.sub_apply, Matrix.one_apply_eq]
    exact sub_le_self 1 n
  exact (mul_le_mul_of_nonneg_left h det0.le).trans_eq (mul_one _)

def locSnoc (n : Nat) : Fin n⊕Unit ≃ Fin (n+1) :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.ofUnique Unit (Fin 1))).trans (finSumFinEquiv (m:=n) (n:=1))

theorem principal_det_le_sum (n : Nat) (M : Matrix (I⊕Fin n) (I⊕Fin n) ℝ)
    (pd : M.PosDef) (diag : ∀ i, M i i=1) :
    M.det ≤ (M.submatrix Sum.inl Sum.inl).det := by
  induction n with
  | zero =>
    let e : I≃I⊕Fin 0 := (Equiv.sumEmpty I (Fin 0)).symm
    have ef : (e : I→I⊕Fin 0)=Sum.inl := rfl
    exact le_of_eq (ef ▸ (Matrix.det_submatrix_equiv_self e M).symm)
  | succ n ih =>
    let e : (I⊕Fin n)⊕Unit ≃ I⊕Fin (n+1) :=
      (Equiv.sumAssoc I (Fin n) Unit).trans (Equiv.sumCongr (Equiv.refl I) (locSnoc n))
    let B := M.submatrix e e
    let C := B.submatrix Sum.inl Sum.inl
    have bpd : B.PosDef := pd.submatrix e.injective
    have cpd : C.PosDef := bpd.submatrix Sum.inl_injective
    have d := unit_border_det_le B bpd (diag _)
    have d' := ih C cpd (fun i => diag (e (.inl i)))
    have bdet : B.det=M.det := Matrix.det_submatrix_equiv_self e M
    have principal : C.submatrix Sum.inl Sum.inl=M.submatrix Sum.inl Sum.inl := by ext i j; rfl
    exact bdet ▸ principal ▸ d.trans d'

theorem principal_det_le (M : Matrix J J ℝ) (f : I ↪ J)
    (pd : M.PosDef) (diag : ∀ i, M i i=1) :
    M.det≤(M.submatrix f f).det := by
  classical
  let P := Set.range f
  let T := ↥(Pᶜ : Set J)
  let _ : Fintype T := Fintype.ofFinite _
  let e : I⊕Fin (Fintype.card T) ≃ J :=
    (Equiv.sumCongr (Equiv.ofInjective f f.injective) (Fintype.equivFin T).symm).trans
      (Equiv.sumCompl (fun x => x ∈ P))
  let B := M.submatrix e e
  have h := principal_det_le_sum _ B (pd.submatrix e.injective) (fun i => diag (e i))
  have bd : B.det=M.det := Matrix.det_submatrix_equiv_self e M
  have px : B.submatrix Sum.inl Sum.inl=M.submatrix f f := by ext i j; rfl
  exact bd ▸ px ▸ h

theorem pd_of_psd_det (M : Matrix I I ℝ)
    (psd : M.PosSemidef) (det0 : M.det≠0) : M.PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨psd.isHermitian,?_⟩
  intro x nx
  have inj := Matrix.mulVec_injective_of_det_ne_zero det0
  have non := psd.dotProduct_mulVec_nonneg x
  apply lt_of_le_of_ne non
  intro h
  have hx := psd.dotProduct_mulVec_zero_iff.mp h.symm
  exact nx (inj (by simpa using hx))

theorem det_pair_upper (M : Matrix I I ℝ)
    (psd : M.PosSemidef) (d0 : M.det≠0) (diag : ∀ i, M i i=1) {i j : I} (ij : i≠j) :
    M.det≤1-(M i j)^2 := by
  let f : Fin 2→I := ![i,j]
  have fi : Function.Injective f := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [f,Ne.symm ij]
  let emb : Fin 2↪I := ⟨f,fi⟩
  have h := principal_det_le M emb (pd_of_psd_det M psd d0) diag
  have sym : M j i=M i j := by
    have k := congrFun (congrFun psd.isHermitian.eq i) j
    simpa [Matrix.conjTranspose_apply] using k
  rw [Matrix.det_fin_two] at h
  simpa [Matrix.submatrix_apply,emb,f,diag,sym,pow_two] using h

#print axioms det_pair_upper
end RobustFolkman.GeometricGap
