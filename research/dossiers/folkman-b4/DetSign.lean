import CriticalKernel
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace FolkmanB4.Critical
open Matrix Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def PositivePattern (I : V → V → Prop) (A : Matrix V V ℚ) : Prop :=
  (∀ i j, I i j → 0<A i j) ∧ (∀ i j, ¬I i j → A i j=0)

omit [Fintype V] in
theorem update_pattern {I : V → V → Prop} {A B : Matrix V V ℚ}
    (hA : PositivePattern I A) (hB : PositivePattern I B) (v : V) :
    PositivePattern I (A.updateRow v (B v)) := by
  constructor
  · intro i j h
    by_cases e : i=v
    · subst i; simpa using hB.1 v j h
    · simpa [Matrix.updateRow_ne e] using hA.1 i j h
  · intro i j h
    by_cases e : i=v
    · subst i; simpa using hB.2 v j h
    · simpa [Matrix.updateRow_ne e] using hA.2 i j h

omit [Fintype V] in
theorem mixed_row_pattern {I : V → V → Prop} {A B : Matrix V V ℚ}
    (hA : PositivePattern I A) (hB : PositivePattern I B) (v : V)
    {p q : ℚ} (hp : 0<p) (hq : 0<q) :
    PositivePattern I (A.updateRow v (p • A v+q • B v)) := by
  constructor
  · intro i j h
    by_cases e : i=v
    · subst i
      simpa using add_pos (mul_pos hp (hA.1 v j h)) (mul_pos hq (hB.1 v j h))
    · simpa [Matrix.updateRow_ne e] using hA.1 i j h
  · intro i j h
    by_cases e : i=v
    · subst i
      simp [hA.2 v j h,hB.2 v j h]
    · simpa [Matrix.updateRow_ne e] using hA.2 i j h

theorem det_update_same_sign {I : V → V → Prop}
    (nonsing : ∀ A, PositivePattern I A → A.det≠0)
    {A B : Matrix V V ℚ} (hA : PositivePattern I A) (hB : PositivePattern I B)
    (v : V) : 0<A.det ↔ 0<(A.updateRow v (B v)).det := by
  let D := (A.updateRow v (B v)).det
  have nda : A.det≠0 := nonsing _ hA
  have ndb : D≠0 := nonsing _ (update_pattern hA hB v)
  have mix (p q : ℚ) (hp : 0<p) (hq : 0<q) : p*A.det+q*D≠0 := by
    have nz := nonsing _ (mixed_row_pattern hA hB v hp hq)
    rwa [det_updateRow_add,det_updateRow_smul,det_updateRow_smul,updateRow_eq_self] at nz
  change 0<A.det ↔ 0<D
  constructor
  · intro a
    by_contra b
    have ne : D<0 := lt_of_le_of_ne (le_of_not_gt b) ndb
    exact mix (-D) A.det (neg_pos.mpr ne) a (by rw [neg_mul,mul_comm D A.det,neg_add_cancel])
  · intro b
    by_contra a
    have ne : A.det<0 := lt_of_le_of_ne (le_of_not_gt a) nda
    exact mix D (-A.det) b (neg_pos.mpr ne) (by rw [mul_comm D A.det,neg_mul,mul_comm A.det D,add_neg_cancel])

/-- A nonsingular positive pattern has a constant determinant sign, proved
by rational row interpolation, with no topological intermediate value lemma. -/
theorem det_same_sign {I : V → V → Prop}
    (nonsing : ∀ A, PositivePattern I A → A.det≠0)
    {A B : Matrix V V ℚ} (hA : PositivePattern I A) (hB : PositivePattern I B) :
    0<A.det ↔ 0<B.det := by
  let splice (S : Finset V) : Matrix V V ℚ := fun i j => if i∈S then B i j else A i j
  have hp (S : Finset V) : PositivePattern I (splice S) := by
    constructor
    · intro i j h; by_cases e : i∈S <;> simp [splice,e,hA.1 i j h,hB.1 i j h]
    · intro i j h; by_cases e : i∈S <;> simp [splice,e,hA.2 i j h,hB.2 i j h]
  have step (S : Finset V) : 0<A.det ↔ 0<(splice S).det := by
    induction S using Finset.induction_on with
    | empty =>
      have e : splice ∅=A := by ext i j; simp [splice]
      rw [e]
    | insert v S _ ih =>
      have e : splice (insert v S)=(splice S).updateRow v (B v) := by
        ext i j
        by_cases h : i=v
        · subst i
          rw [Matrix.updateRow_self]
          simp [splice]
        · rw [Matrix.updateRow_ne h]
          simp [splice,h]
      rw [e]
      exact ih.trans (det_update_same_sign nonsing (hp S) hB v)
  have e : splice univ=B := by ext i j; simp [splice]
  simpa only [e] using step univ

#print axioms det_same_sign
end FolkmanB4.Critical
