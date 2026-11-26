import RibbonStationaryFieldCore
import RibbonAffineModCore

namespace RibbonStationaryField
open RibbonAffine (Mono Row pl delta delta_zero eRow rel_from_mul nf mulP negative poly_eq pl_mul
  pl_append subUV sub_sound)
open RibbonStationaryWord
variable {K : Type*} [Field K]

def natConst (n : Int) : Poly := [(0,0,n)]
def zscale (n : Int) (f : Poly) := mulP (natConst n) f
def add3 (p q r : Poly) := p++q++r

/-- A symbolic integer identity; unlike a resultant, the checker needs only polynomial operations. -/
structure Id where
  a : Poly
  b : Poly
  c : Poly
  d : Poly
  rhs : Poly
  deriving Inhabited

def Id.valid (I : Id) (f g h : Poly) (p : Int) : Prop :=
  nf (add3 (mulP I.a f) (mulP I.b g) (mulP I.c h) ++ zscale p I.d)=nf I.rhs
instance idValidDecidable (I : Id) (f g h : Poly) (p : Int) : Decidable (I.valid f g h p) := by unfold Id.valid; infer_instance

theorem Id.sound (I : Id) (f g h : Poly) (p : Int) (C : I.valid f g h p) (t : Kˣ)
    (F : pl t 1 f=0) (G : pl t 1 g=0) (H : pl t 1 h=0) (P : (p:K)=0) :
    pl t 1 I.rhs=0 := by
  have T := poly_eq t 1 _ _ C
  rw [add3,pl_append,pl_append,pl_append,pl_mul,pl_mul,pl_mul,zscale,pl_mul,F,G,H] at T
  have R : pl t 1 (natConst p)=0 := by simp [natConst,pl, RibbonAffine.mon,P]
  rw [R,zero_mul,mul_zero,mul_zero,mul_zero,add_zero,add_zero,add_zero] at T
  exact T.symm

theorem coprime_drop (n : Nat) (odd : Odd n) (no3 : ¬3∣n) (t : Kˣ)
    (tn : t^n=1) (k : Int) (e u v : Nat) (D : k.natAbs=e*(2^u*3^v)) (tk : t^k=1) :
    t^e=1 := by
  have A := orderOf_dvd_iff_pow_eq_one.mpr tn
  have B : orderOf t ∣ k.natAbs :=
    Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr (orderOf_dvd_iff_zpow_eq_one.mpr tk))
  rw [D] at B
  have h2 := (supported_dvd n odd no3 2 (by decide)).pow_right u
  have h3 := (supported_dvd n odd no3 3 (by decide)).pow_right v
  have C := (h2.mul_right h3).of_dvd_left A
  exact orderOf_dvd_iff_pow_eq_one.mp (C.dvd_of_dvd_mul_right B)

theorem collision_param (u v : Int) (t : Kˣ) (a b : Kˣ) (ha : a=t^v) (hb : b=t^(-u)) (P Q : Row)
    (hit : eRow a b P=eRow a b Q) :
    t^(v*(P.i-Q.i)-u*(P.j-Q.j))=1 ∧ pl t 1 (subUV u v (delta P Q))=0 := by
  have M : a^P.i*b^P.j=a^Q.i*b^Q.j := congrArg (fun s : Bool×Kˣ×K => s.2.1) hit
  have R := rel_from_mul a b P.i P.j Q.i Q.j M
  rw [ha,hb,←zpow_mul,←zpow_mul,←zpow_add] at R
  refine ⟨by convert R using 1 <;> ring,?_⟩
  rw [←sub_sound,←ha,←hb]
  exact delta_zero a b P Q hit

end RibbonStationaryField
#print axioms RibbonStationaryField.Id.sound
#print axioms RibbonStationaryField.coprime_drop
