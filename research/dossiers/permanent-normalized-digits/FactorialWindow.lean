import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-! Valuation window isolating one matching-size coefficient. This does not
formalize the permanent gadget or the parameterized reduction. -/
namespace PermanentValuationWindow
variable (p : ℕ) [hp : Fact p.Prime]

theorem shortVal (L i : ℕ) (hi : 0 < i) (hs : i < p^L) :
    padicValNat p i < L := by
  by_contra! h
  exact (not_le_of_gt hs) (Nat.le_of_dvd hi ((pow_dvd_pow p h).trans pow_padicValNat_dvd))

theorem plusPow (L i : ℕ) (hi : 0 < i) (hs : i < p^L) :
    padicValNat p (p^L+i) = padicValNat p i := by
  have hn : 0 < p^L := pow_pos hp.out.pos L
  have hf : (↑(padicValNat p i) : ℤ) < ↑L := by exact_mod_cast (shortVal p L i hi hs)
  have h := padicValRat.add_eq_of_lt (p:=p) (q:=(i:ℚ)) (r:=((p^L:ℕ):ℚ))
      (by positivity) (by exact_mod_cast hi.ne') (by exact_mod_cast hn.ne')
      (by simpa only [padicValRat.of_nat,padicValNat.prime_pow] using hf)
  rw [add_comm] at h
  rw [← Nat.cast_add, padicValRat.of_nat, padicValRat.of_nat] at h
  exact_mod_cast h

theorem minusPow (L i : ℕ) (hi : 0 < i) (hs : i < p^L) :
    padicValNat p (p^L-i) = padicValNat p i := by
  have hn : 0 < p^L := pow_pos hp.out.pos L
  have hf : (↑(padicValNat p i) : ℤ) < ↑L := by exact_mod_cast (shortVal p L i hi hs)
  have hsum : -(i:ℚ) + ((p^L:ℕ):ℚ) = ((p^L-i:ℕ):ℚ) := by
    rw [Nat.cast_sub hs.le]
    ring
  have h := padicValRat.add_eq_of_lt (p:=p) (q:= -(i:ℚ)) (r:=((p^L:ℕ):ℚ))
      (by rw [hsum]; exact_mod_cast (Nat.sub_ne_zero_of_lt hs))
      (neg_ne_zero.mpr (by exact_mod_cast hi.ne')) (by exact_mod_cast hn.ne')
      (by simpa only [padicValRat.neg,padicValRat.of_nat,padicValNat.prime_pow] using hf)
  rw [hsum, padicValRat.neg, padicValRat.of_nat, padicValRat.of_nat] at h
  exact_mod_cast h

theorem belowFactorial (L j : ℕ) (hj : j ≤ p^L-1) :
    padicValNat p (p^L-1).factorial =
      padicValNat p (p^L-1-j).factorial + padicValNat p j.factorial := by
  induction j with
  | zero => simp
  | succ j ih =>
    have ih := ih (by omega)
    have hstep : p^L-1-j = (p^L-1-(j+1))+1 := by omega
    rw [hstep, Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero _)] at ih
    rw [Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
    have he : (p^L-1-(j+1))+1 = p^L-(j+1) := by omega
    rw [he, minusPow p L (j+1) (by omega) (by omega)] at ih
    omega

theorem aboveFactorial (L j : ℕ) (hj : j < p^L) :
    padicValNat p (p^L+j).factorial =
      padicValNat p (p^L-1).factorial + L + padicValNat p j.factorial := by
  induction j with
  | zero =>
    have hpos : 0 < p^L := pow_pos hp.out.pos L
    have hf : (p^L).factorial = p^L * (p^L-1).factorial := by
      conv_lhs => rw [show p^L = (p^L-1)+1 by omega]
      rw [Nat.factorial_succ, show (p^L-1)+1 = p^L by omega]
    simp [hf, padicValNat.mul hpos.ne' (Nat.factorial_ne_zero _), padicValNat.prime_pow,
      Nat.add_comm]
  | succ j ih =>
    have ih := ih (by omega)
    have hN : p^L+(j+1) = (p^L+j)+1 := by omega
    rw [hN, Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero _),
      Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero _), ih]
    rw [show (p^L+j)+1 = p^L+(j+1) by omega, plusPow p L (j+1) (by omega) hj]
    omega

theorem factorialWindow (L k q : ℕ) (hk : k < L) (hkPow : k < p^L)
    (hq : q ≤ p^L-1+k) (hneq : q ≠ k) :
    k + padicValNat p (p^L-1).factorial <
      q + padicValNat p (p^L-1+k-q).factorial := by
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · let j := k-q-1
    have hj : j < p^L := by dsimp [j]; omega
    rw [show p^L-1+k-q = p^L+j by dsimp [j]; omega, aboveFactorial p L j hj]
    omega
  · let j := q-k
    have hj : j ≤ p^L-1 := by dsimp [j]; omega
    rw [show p^L-1+k-q = p^L-1-j by dsimp [j]; omega]
    have h := belowFactorial p L j hj
    have hsmall := padicValNat_factorial_lt_of_ne_zero p (n:=j) (by dsimp [j]; omega)
    dsimp [j] at h hsmall ⊢
    omega

#print axioms factorialWindow
end PermanentValuationWindow
