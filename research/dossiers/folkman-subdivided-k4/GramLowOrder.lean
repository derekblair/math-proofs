import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.GroupTheory.Perm.Support

namespace RobustFolkman.Gram
open Finset Polynomial
variable {V : Type*} [Fintype V] [DecidableEq V]

def entryOrder (A : V → V → Bool) (i j : V) : Nat :=
  if i=j then 0 else if A i j then 1 else 2

def entryFactor {R : Type*} [CommRing R] (A : V → V → Bool) (B : V → V → R) (i j : V) : R :=
  if i=j ∨ A i j=true then 1 else B i j

noncomputable def gramPolynomial {R : Type*} [CommRing R] (A : V → V → Bool) (B : V → V → R) :
    Matrix V V (Polynomial R) :=
  fun i j => C (entryFactor A B i j)*X^(entryOrder A i j)

theorem order_ge_four_of_nonedge (A : V → V → Bool) (sym : ∀ i j, A i j=A j i)
    (p : Equiv.Perm V) (i : V) (moved : p i≠i) (noedge : A (p i) i=false) :
    4≤∑ j, entryOrder A (p j) j := by
  classical
  have hi : i∈p.support := Equiv.Perm.mem_support.mpr moved
  have np : p≠1 := fun e => moved (by simp [e])
  have supp2 := Equiv.Perm.two_le_card_support_of_ne_one np
  by_cases two : p.support.card=2
  · obtain ⟨x,y,_,rfl⟩ := Equiv.Perm.card_support_eq_two.mp two
    let q := Equiv.swap x y
    let k := q i
    have ki : k≠i := moved
    have kq : q k=i := Equiv.swap_apply_self x y i
    have e1 : entryOrder A (q i) i=2 := by simp [entryOrder,moved,noedge,q]
    have en : A i k=false := by
      rw [sym]
      exact noedge
    have e2 : entryOrder A (q k) k=2 := by rw [kq]; simp [entryOrder,Ne.symm ki,en]
    have sub : ({i,k}:Finset V) ⊆ (univ : Finset V) := subset_univ _
    have bound := sum_le_sum_of_subset_of_nonneg (f:=fun j => entryOrder A (q j) j) sub
      (fun _ _ _ => Nat.zero_le _)
    rw [sum_insert (by simp [Ne.symm ki]),sum_singleton,e1,e2] at bound
    exact bound
  · have three : 3≤p.support.card := by omega
    let g (j : V) := if j=i then 2 else 1
    have sq : ∑ j∈p.support, g j=p.support.card+1 := by
      have eq (j : V) : g j=1+(if j=i then 1 else 0) := by by_cases h : j=i <;> simp [g,h]
      simp_rw [eq,sum_add_distrib]
      simp [hi]
    have bd : (∑ j∈p.support, g j)≤∑ j∈p.support, entryOrder A (p j) j := by
      apply sum_le_sum
      intro j hj
      by_cases h : j=i
      · subst j
        simp [g,entryOrder,moved,noedge]
      · have ne := Equiv.Perm.mem_support.mp hj
        by_cases ej : A (p j) j <;> simp [g,h,entryOrder,ne,ej]
    have inc := sum_le_sum_of_subset_of_nonneg
      (f:=fun j => entryOrder A (p j) j) (subset_univ p.support) (fun _ _ _ => Nat.zero_le _)
    rw [sq] at bd
    omega

theorem gram_product {R : Type*} [CommRing R] (A : V → V → Bool) (B : V → V → R)
    (p : Equiv.Perm V) :
    (∏ j, gramPolynomial A B (p j) j) =
      C (∏ j, entryFactor A B (p j) j)*X^(∑ j, entryOrder A (p j) j) := by
  simp only [gramPolynomial,prod_mul_distrib,map_prod,prod_pow_eq_pow_sum]

/-- Off-diagonal nonedge entries at scale X² cannot affect any
determinant coefficient of degree at most three. -/
theorem determinant_low_independent {R : Type*} [CommRing R]
    (A : V → V → Bool) (sym : ∀ i j, A i j=A j i) (B C' : V → V → R) (d : Nat) (small : d≤3) :
    (gramPolynomial A B).det.coeff d=(gramPolynomial A C').det.coeff d := by
  classical
  rw [Matrix.det_apply,Matrix.det_apply,finsetSum_coeff,finsetSum_coeff]
  apply sum_congr rfl
  intro p _
  by_cases O : ∀ j, p j=j ∨ A (p j) j=true
  · have E (j : V) : gramPolynomial A B (p j) j=gramPolynomial A C' (p j) j := by
      simp [gramPolynomial,entryFactor,O j]
    simp_rw [E]
  · push Not at O
    obtain ⟨j,move,noedge⟩ := O
    have H := order_ge_four_of_nonedge A sym p j move (by simpa using noedge)
    have ne : (∑ j, entryOrder A (p j) j) ≠ d := by omega
    rw [gram_product,gram_product,coeff_smul,coeff_smul,coeff_C_mul_X_pow,coeff_C_mul_X_pow]
    simp [Ne.symm ne]

def adjacencyMatrix (R : Type*) [CommRing R] (A : V → V → Bool) : Matrix V V R :=
  fun i j => if i≠j ∧ A i j=true then 1 else 0

theorem gram_zero_nonedge {R : Type*} [CommRing R] (A : V → V → Bool) :
    gramPolynomial A (fun _ _ => (0:R)) = 1+(X:Polynomial R) • (adjacencyMatrix R A).map C := by
  ext i j
  by_cases e : i=j
  · subst j
    simp [gramPolynomial,entryFactor,entryOrder,adjacencyMatrix,Matrix.one_apply]
  · cases h : A i j <;>
      simp [gramPolynomial,entryFactor,entryOrder,adjacencyMatrix,Matrix.one_apply,e,h]

theorem determinant_low_as_minors {R : Type*} [CommRing R] (A : V → V → Bool)
    (sym : ∀ i j, A i j=A j i) (B : V → V → R) {k : Nat} (small : k≤3) :
    (gramPolynomial A B).det.coeff k =
      ∑ s ∈ (univ : Finset V).powersetCard k,
        ((adjacencyMatrix R A).submatrix (Subtype.val : s → V) (Subtype.val : s → V)).det := by
  rw [determinant_low_independent A sym B (fun _ _ => 0) k small,gram_zero_nonedge]
  exact Matrix.coeff_det_one_add_X_smul_eq_sum_minors _ _

#print axioms determinant_low_independent
#print axioms determinant_low_as_minors
end RobustFolkman.Gram
