import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.Ring
import Mathlib.Data.Matrix.Basic

namespace RobustFolkman.GeometricGap
open Finset Matrix
variable {J : Type*} [Fintype J] [DecidableEq J]

def flipBit (i : J) : (J → Bool) ≃ (J → Bool) where
  toFun b := Function.update b i (!(b i))
  invFun b := Function.update b i (!(b i))
  left_inv b := by
    funext j
    by_cases h : j=i
    · subst j; simp
    · simp [Function.update_of_ne h]
  right_inv b := by
    funext j
    by_cases h : j=i
    · subst j; simp
    · simp [Function.update_of_ne h]

theorem flipBit_toggle (i j : J) (ne : i≠j) (b : J→Bool) (a : ℝ) :
    (if (flipBit i b) i ≠ (flipBit i b) j then a else 0) +
      (if b i ≠ b j then a else 0) = a := by
  change (if (Function.update b i (!(b i))) i ≠ (Function.update b i (!(b i))) j
    then a else 0) + _ = _
  simp only [Function.update_self,Function.update_of_ne ne.symm]
  cases bi : b i <;> cases bj : b j <;> simp [bi,bj]

def crossPart (A : Matrix J J ℝ) (b : J → Bool) : Matrix J J ℝ :=
  fun i j => if b i ≠ b j then A i j else 0

/-- Exactly half of each off-diagonal entry survives a uniform binary
split. Thus the average of the cross-block matrices is A/2. -/
theorem sum_crossParts (A : Matrix J J ℝ) (diag : ∀ i, A i i=0) :
    (2:ℝ) • (∑ b : J → Bool, crossPart A b) = (Fintype.card (J→Bool):ℝ) • A := by
  ext i j
  simp only [Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul]
  by_cases e : i=j
  · subst j
    simp [crossPart,diag i]
  let f := fun b : J→Bool => if b i≠b j then A i j else 0
  change 2*(∑ b, f b)=_
  have sym : (∑ b, f (flipBit i b))=∑ b, f b :=
    (flipBit i).sum_comp f
  have h : (∑ b, (f (flipBit i b)+f b))=∑ _ : J→Bool,A i j :=
    Finset.sum_congr rfl (fun b _ => flipBit_toggle i j e b (A i j))
  rw [Finset.sum_add_distrib,sym] at h
  calc
    _ = (∑ b, f b)+(∑ b, f b) := by ring
    _ = _ := by simpa using h

#print axioms sum_crossParts
end RobustFolkman.GeometricGap
