import Permutation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace PermCircles

def Fits (r : ℝ) (n : ℕ) : Prop :=
  2 ≤ n ∧ ∃ p : Equiv.Perm (Fin n), ∀ i j, i ≠ j →
    4*r^2 ≤ ((i.val : ℝ)-j.val)^2 + (((p i).val : ℝ)-(p j).val)^2

lemma radius_order {r : ℝ} (hr : 1 ≤ r) :
    ∃ n : ℕ, Fits r n ∧ (n:ℝ) ≤
      2*Real.sqrt 3*r^2+(5*Real.sqrt 3+3)*r+(3*Real.sqrt 3+5) := by
  let m := ⌈r⌉
  let S := Real.sqrt 3
  let b := ⌈S*(m:ℝ)⌉+1
  have hS2 : S^2 = 3 := Real.sq_sqrt (by norm_num)
  have hS : 1 ≤ S := by
    have hz : 0 ≤ S := Real.sqrt_nonneg _
    by_contra! h
    nlinarith [mul_nonneg (show 0 ≤ 1-S by linarith) (show 0 ≤ 1+S by linarith)]
  have hmlo : r ≤ (m:ℝ) := Int.le_ceil r
  have hmhi : (m:ℝ) < r+1 := Int.ceil_lt_add_one r
  have hm0 : (1:ℝ) ≤ (m:ℝ) := le_trans hr hmlo
  have hm : 1 ≤ m := by exact_mod_cast hm0
  have hbl : S*(m:ℝ)+1 ≤ (b:ℝ) := by
    dsimp [b]
    push_cast
    linarith [Int.le_ceil (S*(m:ℝ))]
  have hbu : (b:ℝ) ≤ S*(m:ℝ)+2 := by
    dsimp [b]
    push_cast
    linarith [Int.ceil_lt_add_one (S*(m:ℝ))]
  have hbm : (m:ℝ)+1 ≤ (b:ℝ) := by
    have hmul := mul_nonneg (show 0 ≤ S-1 by linarith) (show 0 ≤ (m:ℝ) by linarith)
    linarith
  have hb : m+1 ≤ b := by exact_mod_cast hbm
  have hbq : 3*m^2 ≤ (b-1)^2 := by
    have ht : (S*(m:ℝ))^2 = 3*(m:ℝ)^2 := by linear_combination ((m:ℝ)^2)*hS2
    have hp : 0 ≤ S*(m:ℝ) := mul_nonneg (by linarith) (by linarith)
    have he : (S*(m:ℝ))^2 ≤ ((b:ℝ)-1)^2 := by
      have hne := mul_nonneg (show 0 ≤ (b:ℝ)-1-S*(m:ℝ) by linarith) (show 0 ≤ (b:ℝ)-1+S*(m:ℝ) by linarith)
      nlinarith
    rw [ht] at he
    exact_mod_cast he
  have ho := order_pos hm hb
  refine ⟨(order m b).toNat,⟨?_,modular m b ho,?_⟩,?_⟩
  · have hlarge : 2 ≤ order m b := by
      unfold order
      have hbmul : 0 ≤ (2*m+1)*(b-m-1) := mul_nonneg (by omega) (by omega)
      nlinarith [sq_nonneg m]
    omega
  · intro i j hij
    have hn := modular_distance hm hb hbq i j hij
    have hn' : (2*(m:ℝ))^2 ≤ ((i.val : ℝ)-j.val)^2 +
        (((modular m b ho i).val : ℝ)-(modular m b ho j).val)^2 := by exact_mod_cast hn
    have hmul := mul_nonneg (show 0 ≤ (m:ℝ)-r by linarith) (show 0 ≤ (m:ℝ)+r by linarith)
    nlinarith
  · have hc : ((order m b).toNat : ℝ) = (2*(m:ℝ)+1)*(b:ℝ)-(m:ℝ) := by
      have he := order_cast ho
      unfold order at he
      exact_mod_cast he
    rw [hc]
    have hbmul := mul_nonneg (show 0 ≤ 2*(m:ℝ)+1 by linarith) (show 0 ≤ S*(m:ℝ)+2-(b:ℝ) by linarith)
    have hmm := mul_nonneg (show 0 ≤ r+1-(m:ℝ) by linarith) (show 0 ≤ r+1+(m:ℝ) by linarith)
    have hmm' := mul_nonneg (show 0 ≤ 2*S by linarith) hmm
    have hml := mul_nonneg (show 0 ≤ S+3 by linarith) (show 0 ≤ r+1-(m:ℝ) by linarith)
    change (2*(m:ℝ)+1)*(b:ℝ)-(m:ℝ) ≤ 2*S*r^2+(5*S+3)*r+(3*S+5)
    nlinarith only [hbmul,hmm',hml]

#print axioms radius_order
end PermCircles
