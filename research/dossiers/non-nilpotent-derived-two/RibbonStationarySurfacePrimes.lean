import RibbonStationarySurfaceCore

namespace RibbonStationaryField
open RibbonAffine (pl mon)
variable {K : Type*} [Field K]

theorem surface_eq (a b : Kˣ) (s : pl a b sideA0=0) : (2:K)*(a:K)= -1 := by
  have e : (2:K)*(a:K)+1=0 := by simpa [sideA0,pl,mon] using s
  exact eq_neg_of_add_eq_zero_left e

theorem drop_surface_char (a : Kˣ) (p d e u v n : Nat) (pd : Nat.Prime p)
    (pzero : (p:K)=0) (two : (2:K)≠0) (ae : (2:K)*(a:K)= -1)
    (odd : Odd n) (no3 : ¬3∣n) (an : a^n=1) (c : d=e*(2^u*3^v))
    (H : (p:Int) ∣ (2:Int)^d-(-1:Int)^d)
    (L : ¬ (p:Int) ∣ (2:Int)^e-(-1:Int)^e) : False := by
  letI : CharP K p := (CharP.charP_iff_prime_eq_zero (R:=K) pd).mpr pzero
  have E : (2:K)^d=(-1:K)^d := by
    apply sub_eq_zero.mp
    have z := (CharP.intCast_eq_zero_iff K p _).mpr H
    simpa only [Int.cast_sub,Int.cast_pow,Int.cast_ofNat,Int.cast_neg,Int.cast_one] using z
  have pq (d : Nat) := congrArg (fun x : K => x^d) ae
  have D : a^d=1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    apply mul_left_cancel₀ (pow_ne_zero d two)
    rw [Units.val_one,mul_one]
    simpa only [mul_pow,←E] using pq d
  have B := coprime_drop n odd no3 a an (d:Int) e u v (by simpa using c) (by simpa using D)
  have R := pq e
  rw [mul_pow,←Units.val_pow_eq_pow_val,B,Units.val_one,mul_one] at R
  apply L
  apply (CharP.intCast_eq_zero_iff K p _).mp
  simpa only [Int.cast_sub,Int.cast_pow,Int.cast_ofNat,Int.cast_neg,Int.cast_one] using sub_eq_zero.mpr R

theorem surface_11_a (a : Kˣ) (P : (11:K)=0) (two : (2:K)≠0) (ae : (2:K)*(a:K)= -1) : (a:K)=5 := by
  apply mul_left_cancel₀ two
  rw [ae]
  linear_combination -P

theorem surface_binom_val (a b : Kˣ) (e : Nat) : pl a b (surfaceBinom e)=((b:K)^e)-1 := by
  simp [surfaceBinom,pl,mon,sub_eq_add_neg]

theorem surface_11_b (a b : Kˣ) (P : (11:K)=0) (odd : Odd n) (no3 : ¬3∣n) (B : b^n=1)
    (E : pl a b (surfaceBinom 10)=0) :
    (b:K)=1 ∨ (b:K)=3 ∨ (b:K)=4 ∨ (b:K)=5 ∨ (b:K)=9 := by
  have b10 : b^10=1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    exact sub_eq_zero.mp (by simpa [surface_binom_val] using E)
  have b5 := coprime_drop n odd no3 b B 10 5 1 0 (by decide) (by simpa using b10)
  have c : (b:K)^5=1 := by simpa using congrArg (fun u : Kˣ => (u:K)) b5
  have f : ((b:K)-1)*((b:K)-3)*((b:K)-4)*((b:K)-5)*((b:K)-9)=0 := by
    linear_combination c + (-(2:K)*(b:K)^4 + 16*(b:K)^3 - 58*(b:K)^2 + 93*(b:K) - 49)*P
  simpa only [mul_eq_zero,sub_eq_zero,or_assoc] using f

theorem surface_43_b (b : Kˣ) (P : (43:K)=0) (two : (2:K)≠0) (odd : Odd n) (B : b^n=1)
    (E : (b:K)^2 - (b:K) - 2=0) : False := by
  have Q : ((b:K)+1)*((b:K)-2)=0 := by linear_combination E
  rcases mul_eq_zero.mp Q with H|H
  · apply RibbonAffine.avoid_neg b n odd B two 1
    simpa only [zpow_one] using eq_neg_of_add_eq_zero_left H
  · have h : (b:K)=2 := sub_eq_zero.mp H
    apply RibbonAffine.avoid_neg b n odd B two 7
    rw [Units.val_zpow_eq_zpow_val,h]
    change (2:K)^((7:Nat):Int) = -1
    rw [zpow_natCast]
    linear_combination 3*P

end RibbonStationaryField
#print axioms RibbonStationaryField.drop_surface_char
#print axioms RibbonStationaryField.surface_11_b
