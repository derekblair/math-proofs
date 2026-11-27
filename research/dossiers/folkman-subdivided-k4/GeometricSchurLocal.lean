import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace RobustFolkman.GeometricGap
open Finset Matrix
variable {K I : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem bounded_dot (b x : I→K) (ε M : K) (e0 : 0≤ε)
    (hb : ∀ i, |b i|≤ε) (hx : ∀ i, |x i|≤M) :
    |b ⬝ᵥ x| ≤ (Fintype.card I : K)*ε*M := by
  unfold dotProduct
  calc
    _ ≤ ∑ i, |b i*x i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : I, ε*M := sum_le_sum fun i _ => by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hb i) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hx i) e0)
    _ = _ := by simp [mul_assoc]

theorem near_identity_solve_bound (A : Matrix I I K) (x c : I→K) (ε : K) (e0 : 0≤ε)
    (rad : 0<1-(Fintype.card I : K)*ε)
    (entry : ∀ i j, |A i j-(1 : Matrix I I K) i j|≤ε)
    (hc : ∀ i, |c i|≤ε) (sol : A *ᵥ x=c) :
    ∀ i, |x i|≤ε/(1-(Fintype.card I : K)*ε) := by
  intro i
  have ne : (univ : Finset I).Nonempty := ⟨i,mem_univ _⟩
  obtain ⟨k,_,kh⟩ := exists_max_image (univ : Finset I) (fun j => |x j|) ne
  let R : Matrix I I K := A-1
  have hR : ∀ j, |R k j|≤ε := fun j => entry k j
  have hcalc : x k+R k ⬝ᵥ x=c k := by
    have Aeq : A=1+R := by unfold R; abel
    have eq := congrFun sol k
    nth_rw 1 [Aeq] at eq
    rwa [Matrix.add_mulVec,Matrix.one_mulVec,Pi.add_apply] at eq
  have row := bounded_dot (R k) x ε |x k| e0 hR (fun j => kh j (mem_univ j))
  have absrow : |x k|≤ ε+(Fintype.card I : K)*ε*|x k| := by
    have xeq : x k=c k-R k ⬝ᵥ x := eq_sub_of_add_eq hcalc
    have triangle : |c k - R k ⬝ᵥ x|≤|c k|+|R k ⬝ᵥ x| := by
      rw [sub_eq_add_neg]
      simpa only [abs_neg] using abs_add_le (c k) (-(R k ⬝ᵥ x))
    exact (congrArg abs xeq).le.trans (triangle.trans (add_le_add (hc k) row))
  apply (kh i (mem_univ i)).trans
  apply (le_div_iff₀ rad).mpr
  linarith only [absrow]

theorem schur_prediction_bound (A : Matrix I I K) [Invertible A]
    (B : Matrix I (Fin 2) K) (ε : K) (e0 : 0≤ε)
    (rad : 0<1-(Fintype.card I : K)*ε)
    (entry : ∀ i j, |A i j-(1 : Matrix I I K) i j|≤ε)
    (small : ∀ i j, |B i j|≤ε) (a b : Fin 2) :
    |(B.transpose*⅟A*B) a b| ≤ (Fintype.card I : K)*ε*(ε/(1-(Fintype.card I : K)*ε)) := by
  let c : I→K := fun i => B i b
  let x := (⅟A) *ᵥ c
  have sol : A *ᵥ x=c := by unfold x; rw [Matrix.mulVec_mulVec]; simp
  have vals := near_identity_solve_bound A x c ε e0 rad entry (fun i => small i b) sol
  rw [Matrix.mul_assoc]
  change |(fun i => B i a) ⬝ᵥ x|≤_
  exact bounded_dot _ _ _ _ e0 (fun i => small i a) vals

def setAnchor (s : K) : Matrix (Fin 2) (Fin 2) K := Matrix.of ![![1,s],![s,1]]

def anchorBlock (A : Matrix I I K) (B : Matrix I (Fin 2) K) (s : K) :
    Matrix (I⊕Fin 2) (I⊕Fin 2) K :=
  Matrix.fromBlocks A B B.transpose (setAnchor s)

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem anchor_det (A : Matrix I I K) [Invertible A] (B : Matrix I (Fin 2) K) (s : K) :
    let W := B.transpose * ⅟A * B
    (anchorBlock A B s).det=A.det*((1-W 0 0)*(1-W 1 1)-(s-W 0 1)*(s-W 1 0)) := by
  rw [anchorBlock,Matrix.det_fromBlocks₁₁]
  congr 1
  rw [Matrix.det_fin_two]
  simp [setAnchor]

theorem anchor_center_strict (A : Matrix I I K) [Invertible A] (B : Matrix I (Fin 2) K)
    (det0 : 0<A.det) (s : K) :
    let W := B.transpose*⅟A*B
    let center := (W 0 1+W 1 0)/2
    s≠center → (anchorBlock A B s).det<(anchorBlock A B center).det := by
  intro W center h
  rw [anchor_det,anchor_det]
  apply mul_lt_mul_of_pos_left _ det0
  change (1-W 0 0)*(1-W 1 1)-(s-W 0 1)*(s-W 1 0) <
    (1-W 0 0)*(1-W 1 1)-(center-W 0 1)*(center-W 1 0)
  have h₁ : 0<(s-center)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr h)
  have h₂ : (s-W 0 1)*(s-W 1 0) - (center-W 0 1)*(center-W 1 0)=(s-center)^2 := by
    dsimp [center]
    ring
  linarith only [h₁,h₂]

theorem anchor_clip_strict (A : Matrix I I K) [Invertible A]
    (B : Matrix I (Fin 2) K) (det0 : 0<A.det) (s t : K) (st : t<s)
    (w01 : (B.transpose*⅟A*B) 0 1<t) (w10 : (B.transpose*⅟A*B) 1 0<t) :
    (anchorBlock A B s).det<(anchorBlock A B t).det := by
  rw [anchor_det,anchor_det]
  apply mul_lt_mul_of_pos_left _ det0
  apply sub_lt_sub_left
  have h₁ : t-(B.transpose*⅟A*B) 0 1 < s-(B.transpose*⅟A*B) 0 1 := sub_lt_sub_right st _
  have h₂ : t-(B.transpose*⅟A*B) 1 0 < s-(B.transpose*⅟A*B) 1 0 := sub_lt_sub_right st _
  exact mul_lt_mul_of_pos_right h₁ (sub_pos.mpr w10) |>.trans
    (mul_lt_mul_of_pos_left h₂ (sub_pos.mpr (w01.trans st)))

#print axioms schur_prediction_bound
#print axioms anchor_center_strict
#print axioms anchor_clip_strict
end RobustFolkman.GeometricGap
