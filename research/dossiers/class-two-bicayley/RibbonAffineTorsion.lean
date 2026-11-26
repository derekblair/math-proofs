import RibbonAffinePoly

namespace RibbonAffine
variable {K : Type*} [Field K]

theorem unit_pow_ok (a b : Kˣ) (n : Nat) (ha : a^n=1) (hb : b^n=1) (u v : ℤ) :
    (a^u*b^v)^n=1 := by
  rw [mul_pow,←zpow_natCast,←zpow_mul,Int.mul_comm u, zpow_mul,zpow_natCast,ha,one_zpow,
    one_mul,←zpow_natCast,←zpow_mul,Int.mul_comm v,zpow_mul,zpow_natCast,hb,one_zpow]

theorem avoid_neg (t : Kˣ) (n : Nat) (odd : Odd n) (h : t^n=1)
    (two : (2:K)≠0) (j : ℤ) : ((t^j : Kˣ):K)≠ -1 := by
  intro E
  have M : (t^j)^n=1 := by
    rw [←zpow_natCast,←zpow_mul,Int.mul_comm j,zpow_mul,zpow_natCast,h,one_zpow]
  have F := congrArg (fun u : Kˣ => (u:K)) M
  rw [Units.val_pow_eq_pow_val,E,show ((1:Kˣ):K)=1 from rfl,odd.neg_pow,one_pow] at F
  exact two (by linear_combination -F)

theorem pow_two_drop (t : Kˣ) (n : Nat) (odd : Odd n) (h : t^n=1) (e : t^2=1) : t=1 :=
  orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes odd.coprime_two_right
    (orderOf_dvd_iff_pow_eq_one.mpr h) (orderOf_dvd_iff_pow_eq_one.mpr e))

theorem zpow_drop (t : Kˣ) (n : Nat) (odd : Odd n) (h : t^n=1) (d : ℤ)
    (D : d=1 ∨ d= -1 ∨ d=2 ∨ d= -2) (e : t^d=1) : t=1 := by
  rcases D with rfl|rfl|rfl|rfl
  · simpa using e
  · simpa using e
  · exact pow_two_drop t n odd h (by simpa using e)
  · have H : t^(2:Nat)=1 := by simpa [zpow_neg] using e
    exact pow_two_drop t n odd h H

theorem rel_from_mul (a b : Kˣ) (i j I J : ℤ) (e : a^i*b^j=a^I*b^J) :
    a^(i-I)*b^(j-J)=1 := by
  calc
    _ = (a^i*b^j) * (a^I*b^J)⁻¹ := by simp only [zpow_sub,mul_inv_rev]; ac_rfl
    _ = 1 := by rw [e,mul_inv_cancel]

theorem rel_drop (a b : Kˣ) (n : Nat) (ha : a^n=1) (hb : b^n=1) (o : Odd n)
    (u v d : ℤ) (D : d=1 ∨ d= -1 ∨ d=2 ∨ d= -2)
    (h : a^(u*d)*b^(v*d)=1) : a^u*b^v=1 := by
  apply zpow_drop (a^u*b^v) n o (unit_pow_ok a b n ha hb u v) d D
  rw [mul_zpow,←zpow_mul,←zpow_mul,h]

theorem parametric (a b : Kˣ) (u v p q : ℤ) (bez : p*v-q*u=1)
    (rel : a^u*b^v=1) :
    let t := a^p*b^q
    a=t^v ∧ b=t^(-u) := by
  dsimp only
  have E : b^v=a^(-u) := by
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_right rel
  have F : a^u=b^(-v) := by
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_left rel
  constructor
  · rw [mul_zpow,←zpow_mul a,←zpow_mul b,show q*v=v*q by ring,
      show b^(v*q)=(b^v)^q from zpow_mul b v q,E,←zpow_mul,←zpow_add,show p*v+ -u*q=1 by linarith,zpow_one]
  · rw [mul_zpow,←zpow_mul,show p*(-u)=-(u*p) by ring,
      zpow_neg,zpow_mul,F,←zpow_mul,←zpow_neg,←zpow_mul,←zpow_add,
      show -(-v*p)+q*(-u)=1 by linarith,zpow_one]

end RibbonAffine
#print axioms RibbonAffine.parametric
