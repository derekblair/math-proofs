import RibbonStationaryBaseData
import RibbonStationaryBezout

namespace RibbonAllOddField
open RibbonStationaryField (Poly Id natConst binom binom_val collision_param)
open RibbonAffine (Row pl nf mulP poly_eq pl_mul eRow delta subUV)
variable {K : Type*} [Field K]

theorem odd_drop (n : Nat) (odd : Odd n) (t : Kˣ) (tn : t^n=1)
    (k : Int) (e u : Nat) (D : k.natAbs=e*2^u) (tk : t^k=1) : t^e=1 := by
  have A := orderOf_dvd_iff_pow_eq_one.mpr tn
  have B : orderOf t ∣ k.natAbs :=
    Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr (orderOf_dvd_iff_zpow_eq_one.mpr tk))
  rw [D] at B
  have C := (odd.coprime_two_right.pow_right u).of_dvd_left A
  exact orderOf_dvd_iff_pow_eq_one.mp (C.dvd_of_dvd_mul_right B)

structure Transition where
  x2 : Nat
  x3 : Nat
  e : Nat
  shift : Int
  tr : Poly
  deriving Inhabited

def transitionValid (u v : Int) (P Q : Row) (w : Transition) : Prop :=
  (v*(P.i-Q.i)-u*(P.j-Q.j)).natAbs=w.e*2^w.x2 ∧
    nf (mulP [(w.shift,0,1)] (subUV u v (delta P Q)))=nf w.tr
instance (u v : Int) (P Q : Row) (w : Transition) :
    Decidable (transitionValid u v P Q w) := by unfold transitionValid; infer_instance

theorem transition_sound (u v : Int) (t : Kˣ) (a b : Kˣ) (n : Nat)
    (odd : Odd n) (tn : t^n=1) (ha : a=t^v) (hb : b=t^(-u))
    (P Q : Row) (w : Transition) (V : transitionValid u v P Q w)
    (hit : eRow a b P=eRow a b Q) : pl t 1 (binom w.e)=0 ∧ pl t 1 w.tr=0 := by
  have ⟨d,z⟩ := collision_param u v t a b ha hb P Q hit
  have te := odd_drop n odd t tn _ _ _ V.1 d
  have A := poly_eq t 1 _ _ V.2
  rw [pl_mul,z,mul_zero] at A
  exact ⟨by simp [binom_val,te],A.symm⟩

structure SlopeID where
  n : Int
  wit : Id
  deriving Inhabited

def slopeValid (f : Poly) (w : Transition) (I : SlopeID) : Prop :=
  I.wit.rhs=natConst I.n ∧ I.wit.valid f w.tr (binom w.e) 0
instance (f : Poly) (w : Transition) (I : SlopeID) :
    Decidable (slopeValid f w I) := by unfold slopeValid; infer_instance

theorem slope_sound (t : Kˣ) (f : Poly) (w : Transition) (I : SlopeID) (V : slopeValid f w I)
    (F : pl t 1 f=0) (G : pl t 1 w.tr=0) (B : pl t 1 (binom w.e)=0) : (I.n:K)=0 := by
  have w := I.wit.sound f w.tr (binom w.e) 0 V.2 t F G B (by simp)
  rw [V.1] at w
  simpa [natConst,pl,RibbonAffine.mon] using w

/-- Terminal certificate: an excluded factor forces t to have a certain
order, then a Bézout identity at the coprime-reduced order rules it out. -/
structure Reject where
  e : Nat
  d : Nat
  twoPow : Nat
  threePow : Nat
  order : Id
  empty : Id
  deriving Inhabited

def rejectValid (p : Int) (f : Poly) (r : Reject) : Prop :=
  r.e=r.d*2^r.twoPow ∧ r.order.rhs=binom r.e ∧ r.empty.rhs=natConst 1 ∧
    r.order.valid f [] [] p ∧ r.empty.valid f (binom r.d) [] p
instance (p : Int) (f : Poly) (r : Reject) :
    Decidable (rejectValid p f r) := by unfold rejectValid; infer_instance

theorem reject_sound (p : Int) (f : Poly) (r : Reject) (V : rejectValid p f r)
    (t : Kˣ) (n : Nat) (odd : Odd n) (tn : t^n=1) (P : (p:K)=0)
    (F : pl t 1 f=0) : False := by
  have H := r.order.sound f [] [] p V.2.2.2.1 t F (by rfl) (by rfl) P
  rw [V.2.1,binom_val] at H
  have e : t^r.e=1 := Units.ext (sub_eq_zero.mp H)
  have d := odd_drop n odd t tn (r.e:Int) r.d r.twoPow
    (by simpa using V.1) (by simpa using e)
  have B : pl t 1 (binom r.d)=0 := by simp [binom_val,d]
  have C := r.empty.sound f (binom r.d) [] p V.2.2.2.2 t F B (by rfl) P
  rw [V.2.2.1] at C
  exact (one_ne_zero : (1:K)≠0) (by simpa [natConst,pl,RibbonAffine.mon] using C)

end RibbonAllOddField
#print axioms RibbonAllOddField.transition_sound
#print axioms RibbonAllOddField.reject_sound
