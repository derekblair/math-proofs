import GramLowOrder
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace RobustFolkman.Gram
open Finset Polynomial Matrix

variable {V R : Type*} [Fintype V] [DecidableEq V] [CommRing R]

def CompleteOn (A : V → V → Bool) (s : Finset V) : Prop :=
  ∀ a∈s, ∀ b∈s, a≠b → A a b=true

theorem complete_reindex (A : V → V → Bool) {s : Finset V} {k : Nat}
    (e : Fin k ≃ s) :
    CompleteOn A s ↔ (∀ i j, i≠j → A (e i).val (e j).val=true) := by
  constructor
  · intro h i j ne
    exact h _ (e i).property _ (e j).property (fun q => ne (e.injective (Subtype.ext q)))
  · intro h a ha b hb ne
    obtain ⟨i,ii⟩ := e.surjective ⟨a,ha⟩
    obtain ⟨j,jj⟩ := e.surjective ⟨b,hb⟩
    apply (show A (e i).val (e j).val=true ↔ A a b=true by rw [ii,jj]).mp
    apply h
    intro q
    apply ne
    exact congrArg Subtype.val (ii.symm.trans ((congrArg e q).trans jj))

theorem complete_two (A : V → V → Bool) (sym : ∀ i j, A i j=A j i)
    {s : Finset V} (e : Fin 2 ≃ s) :
    CompleteOn A s ↔ A (e 0).val (e 1).val=true := by
  rw [complete_reindex A e]
  constructor
  · intro h
    exact h 0 1 (by decide)
  · intro h i j ne
    have H : A (e 1).val (e 0).val=true := by rw [sym]; exact h
    fin_cases i <;> fin_cases j <;> first | contradiction | exact h | exact H

theorem complete_three (A : V → V → Bool) (sym : ∀ i j, A i j=A j i)
    {s : Finset V} (e : Fin 3 ≃ s) :
    CompleteOn A s ↔
      A (e 0).val (e 1).val=true ∧ A (e 0).val (e 2).val=true ∧
      A (e 1).val (e 2).val=true := by
  rw [complete_reindex A e]
  constructor
  · intro h
    exact ⟨h 0 1 (by decide),h 0 2 (by decide),h 1 2 (by decide)⟩
  · rintro ⟨h₁,h₂,h₃⟩ i j ne
    have H₁ : A (e 1).val (e 0).val=true := by rw [sym]; exact h₁
    have H₂ : A (e 2).val (e 0).val=true := by rw [sym]; exact h₂
    have H₃ : A (e 2).val (e 1).val=true := by rw [sym]; exact h₃
    fin_cases i <;> fin_cases j <;>
      first | contradiction | exact h₁ | exact h₂ | exact h₃ | exact H₁ | exact H₂ | exact H₃

theorem minor_two (A : V → V → Bool) (sym : ∀ i j, A i j=A j i) (s : Finset V) (hs : s.card=2)
    [Decidable (CompleteOn A s)] :
    ((adjacencyMatrix R A).submatrix (Subtype.val : s → V) (Subtype.val : s → V)).det =
      if CompleteOn A s then -1 else 0 := by
  let e := (Finset.equivFinOfCardEq hs).symm
  let D := (adjacencyMatrix R A).submatrix (Subtype.val : s → V) (Subtype.val : s → V)
  change D.det = _
  rw [←Matrix.det_submatrix_equiv_self e D,Matrix.det_fin_two]
  have e01 : (e 0).val≠(e 1).val := fun h => (by decide : (0:Fin 2)≠1)
    (e.injective (Subtype.ext h))
  have s10 : A (e 1).val (e 0).val=A (e 0).val (e 1).val := sym _ _
  rw [if_congr (complete_two A sym e) rfl rfl]
  cases h : A (e 0).val (e 1).val <;>
    simp [D,Matrix.submatrix_apply,adjacencyMatrix,e01,Ne.symm e01,s10,h]

theorem minor_three (A : V → V → Bool) (sym : ∀ i j, A i j=A j i) (s : Finset V) (hs : s.card=3)
    [Decidable (CompleteOn A s)] :
    ((adjacencyMatrix R A).submatrix (Subtype.val : s → V) (Subtype.val : s → V)).det =
      if CompleteOn A s then (2:R) else 0 := by
  let e := (Finset.equivFinOfCardEq hs).symm
  let D := (adjacencyMatrix R A).submatrix (Subtype.val : s → V) (Subtype.val : s → V)
  change D.det = _
  rw [←Matrix.det_submatrix_equiv_self e D,Matrix.det_fin_three]
  have ex (i j : Fin 3) (ne : i≠j) : (e i).val≠(e j).val :=
    fun q => ne (e.injective (Subtype.ext q))
  have e01 := ex 0 1 (by decide)
  have e02 := ex 0 2 (by decide)
  have e12 := ex 1 2 (by decide)
  have s10 : A (e 1).val (e 0).val=A (e 0).val (e 1).val := sym _ _
  have s20 : A (e 2).val (e 0).val=A (e 0).val (e 2).val := sym _ _
  have s21 : A (e 2).val (e 1).val=A (e 1).val (e 2).val := sym _ _
  rw [if_congr (complete_three A sym e) rfl rfl]
  cases h₁ : A (e 0).val (e 1).val <;> cases h₂ : A (e 0).val (e 2).val <;>
    cases h₃ : A (e 1).val (e 2).val <;>
    simp [D,Matrix.submatrix_apply,adjacencyMatrix,e01,e02,e12,Ne.symm e01,Ne.symm e02,Ne.symm e12,
      s10,s20,s21,h₁,h₂,h₃] <;> ring

theorem degree_two_count (A : V → V → Bool) (sym : ∀ i j, A i j=A j i)
    (B : V → V → R) [DecidablePred (CompleteOn A)] :
    (gramPolynomial A B).det.coeff 2 =
      -(↑(((univ : Finset V).powersetCard 2).filter (CompleteOn A)).card : R) := by
  rw [determinant_low_as_minors A sym B (by decide)]
  have E : (∑ s∈(univ : Finset V).powersetCard 2,
      ((adjacencyMatrix R A).submatrix (Subtype.val : s → V) (Subtype.val : s → V)).det) =
        ∑ s∈(univ : Finset V).powersetCard 2, if CompleteOn A s then (-1:R) else 0 := by
    apply sum_congr rfl
    intro s hs
    exact minor_two A sym s (mem_powersetCard.mp hs).2
  rw [E,←sum_filter]
  simp

theorem degree_three_count (A : V → V → Bool) (sym : ∀ i j, A i j=A j i)
    (B : V → V → R) [DecidablePred (CompleteOn A)] :
    (gramPolynomial A B).det.coeff 3 =
      2*(↑(((univ : Finset V).powersetCard 3).filter (CompleteOn A)).card : R) := by
  rw [determinant_low_as_minors A sym B (by decide)]
  have E : (∑ s∈(univ : Finset V).powersetCard 3,
      ((adjacencyMatrix R A).submatrix (Subtype.val : s → V) (Subtype.val : s → V)).det) =
        ∑ s∈(univ : Finset V).powersetCard 3, if CompleteOn A s then (2:R) else 0 := by
    apply sum_congr rfl
    intro s hs
    exact minor_three A sym s (mem_powersetCard.mp hs).2
  rw [E,←sum_filter]
  simp [nsmul_eq_mul,mul_comm]

theorem degree_zero_one (A : V → V → Bool) (sym : ∀ i j, A i j=A j i)
    (B : V → V → R) :
    (gramPolynomial A B).det.coeff 0=(1:R) ∧ (gramPolynomial A B).det.coeff 1=0 := by
  constructor
  · rw [determinant_low_independent A sym B (fun _ _ => 0) 0 (by decide),gram_zero_nonedge]
    rw [Polynomial.coeff_zero_eq_eval_zero,eval_det_add_X_smul,Matrix.det_one,Polynomial.eval_one]
  · rw [determinant_low_independent A sym B (fun _ _ => 0) 1 (by decide),gram_zero_nonedge]
    simp [Matrix.coeff_det_one_add_X_smul_one,Matrix.trace,adjacencyMatrix]

#print axioms degree_zero_one
#print axioms degree_two_count
#print axioms degree_three_count
end RobustFolkman.Gram
