import RibbonD3FieldSlopeCore

namespace RibbonD3Wide
open RibbonAffine (pl mon poly_eq pl_mul subUV delta avoid_neg eRow Row)
open RibbonStationaryField (Poly binom binom_val Transition transitionValid collision_param supported_dvd)
variable {K : Type*} [Field K]

/-- An odd exponent allows stripping powers of two, but not powers of three. -/
theorem drop_two (t : Kˣ) (n : Nat) (odd : Odd n) (tn : t^n=1)
    (k : Int) (d v : Nat) (D : k.natAbs=d*2^v) (tk : t^k=1) : t^d=1 := by
  have A := orderOf_dvd_iff_pow_eq_one.mpr tn
  have B : orderOf t ∣ k.natAbs :=
    Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr (orderOf_dvd_iff_zpow_eq_one.mpr tk))
  rw [D] at B
  have C := (odd.coprime_two_right.pow_right v).of_dvd_left A
  exact orderOf_dvd_iff_pow_eq_one.mp (C.dvd_of_dvd_mul_right B)

theorem transition_sound (u v : Int) (t : Kˣ) (a b : Kˣ) (n : Nat)
    (odd : Odd n) (tn : t^n=1) (ha : a=t^v) (hb : b=t^(-u))
    (P Q : Row) (w : Transition) (zero : w.x3=0) (V : transitionValid u v P Q w)
    (hit : eRow a b P=eRow a b Q) : pl t 1 (binom w.e)=0 ∧ pl t 1 w.tr=0 := by
  have ⟨d,z⟩ := collision_param u v t a b ha hb P Q hit
  have te := drop_two t n odd tn _ _ w.x2 (by simpa only [zero,pow_zero,mul_one] using V.1) d
  have A := poly_eq t 1 _ _ V.2
  rw [pl_mul,z,mul_zero] at A
  exact ⟨by simp [binom_val,te],A.symm⟩

/-- The already generated base drops are exactly Φ₂, Φ₄ and Φ₆. An odd-order
unit cannot be a root of any of them, including in the presence of 3-torsion. -/
def DropProfile (f : Poly) : Prop :=
  f=[(0,0,1),(1,0,1)] ∨ f=[(0,0,1),(2,0,1)] ∨ f=[(0,0,1),(1,0,-1),(2,0,1)]
instance wideDropProfileDecidable (f : Poly) : Decidable (DropProfile f) := by unfold DropProfile; infer_instance

theorem drop_profile_sound (t : Kˣ) (n : Nat) (odd : Odd n) (tn : t^n=1) (two : (2:K)≠0)
    (f : Poly) (H : DropProfile f) (z : pl t 1 f=0) : False := by
  have z2 : ((t^(2:ℤ):Kˣ):K)=(t:K)^2 := by norm_cast
  have z3 : ((t^(3:ℤ):Kˣ):K)=(t:K)^3 := by norm_cast
  rcases H with rfl|rfl|rfl
  · apply avoid_neg t n odd tn two 1
    have h : (t:K)+1=0 := by simpa [pl,mon,add_comm] using z
    simpa using eq_neg_of_add_eq_zero_left h
  · apply avoid_neg t n odd tn two 2
    have h : (t:K)^2+1=0 := by simpa [pl,mon,add_comm,z2] using z
    simpa [z2] using eq_neg_of_add_eq_zero_left h
  · apply avoid_neg t n odd tn two 3
    have h : (t:K)^2-(t:K)+1=0 := by
      have Y : 1-(t:K)+(t:K)^2=0 := by
        simpa [pl,mon,sub_eq_add_neg,add_assoc,z2] using z
      linear_combination Y
    have H : (t:K)^3+1=0 := by linear_combination ((t:K)+1)*h
    simpa [z3] using eq_neg_of_add_eq_zero_left H

end RibbonD3Wide
#print axioms RibbonD3Wide.drop_two
#print axioms RibbonD3Wide.transition_sound
#print axioms RibbonD3Wide.drop_profile_sound
