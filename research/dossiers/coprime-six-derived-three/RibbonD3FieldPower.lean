import RibbonD3FieldBaseCore

namespace RibbonD3Field
open RibbonAffine (pl mon nf mulP poly_eq pl_mul pl_append)
open RibbonStationaryField (Poly natConst zscale)
variable {K : Type*} [Field K]

/-- A polynomial reduction modulo both an integer and a polynomial. -/
structure ModReduction where
  out : Poly
  mul : Poly
  debt : Poly
  deriving Inhabited

def ModReduction.ok (p : Int) (f u : Poly) (M : ModReduction) : Prop :=
  nf u = nf (M.out ++ mulP M.mul f ++ zscale p M.debt)
instance (p : Int) (f u : Poly) (M : ModReduction) : Decidable (M.ok p f u) := by
  unfold ModReduction.ok
  infer_instance

theorem ModReduction.sound (p : Int) (f u : Poly) (M : ModReduction) (V : M.ok p f u)
    (t : Kˣ) (P : (p:K)=0) (Q : pl t 1 f=0) :
    pl t 1 u=pl t 1 M.out := by
  have I := poly_eq t 1 _ _ V
  rw [pl_append,pl_append,pl_mul,zscale,pl_mul,Q,mul_zero,add_zero] at I
  have N : pl t 1 (natConst p)=0 := by simp [natConst,pl,mon,P]
  rwa [N,zero_mul,add_zero] at I

structure PowerStep where
  bit : Bool
  reduction : ModReduction
  deriving Inhabited

def squareInput (base r : Poly) (bit : Bool) : Poly :=
  if bit then mulP (mulP r r) base else mulP r r

def stepPower (e : Nat) (bit : Bool) : Nat := 2*e + if bit then 1 else 0

def runPower : Nat → List PowerStep → Nat
  | e, [] => e
  | e, s::ss => runPower (stepPower e s.bit) ss

def endPower : Poly → List PowerStep → Poly
  | z, [] => z
  | _, s::ss => endPower s.reduction.out ss

def checkPower (p : Int) (f base : Poly) : Poly → List PowerStep → Bool
  | _, [] => true
  | r, s::ss =>
    decide (s.reduction.ok p f (squareInput base r s.bit)) &&
      checkPower p f base s.reduction.out ss

theorem power_loop (p : Int) (f base r : Poly) (e : Nat) (steps : List PowerStep) (t : Kˣ)
    (P : (p:K)=0) (F : pl t 1 f=0) (R : pl t 1 r=(pl t 1 base)^e)
    (H : checkPower p f base r steps=true) :
    pl t 1 (endPower r steps)=(pl t 1 base)^(runPower e steps) := by
  induction steps generalizing r e with
  | nil => exact R
  | cons s ss ih =>
    have ⟨h,Hs⟩ := Bool.and_eq_true_iff.mp H
    have J := s.reduction.sound p f (squareInput base r s.bit) (of_decide_eq_true h) t P F
    have next : pl t 1 s.reduction.out=(pl t 1 base)^(stepPower e s.bit) := by
      rw [←J]
      cases z : s.bit
      · simp [squareInput,z,pl_mul,R,stepPower,Nat.mul_comm,pow_mul,pow_two]
      · simp [squareInput,z,pl_mul,R,stepPower,Nat.mul_comm,pow_add,pow_mul,pow_two]
    exact ih s.reduction.out (stepPower e s.bit) next Hs

structure PowerCert where
  steps : List PowerStep
  deriving Inhabited

def PowerCert.ok (p : Int) (f base : Poly) (n : Nat) (out : Poly) (C : PowerCert) : Prop :=
  runPower 0 C.steps=n ∧ endPower (natConst 1) C.steps=out ∧
    checkPower p f base (natConst 1) C.steps=true
instance (p : Int) (f base : Poly) (n : Nat) (out : Poly) (C : PowerCert) :
    Decidable (C.ok p f base n out) := by unfold PowerCert.ok; infer_instance

theorem PowerCert.sound (p : Int) (f base : Poly) (n : Nat) (out : Poly) (C : PowerCert)
    (V : C.ok p f base n out) (t : Kˣ) (P : (p:K)=0) (F : pl t 1 f=0) :
    pl t 1 out=(pl t 1 base)^n := by
  have G := power_loop p f base (natConst 1) 0 C.steps t P F (by simp [natConst,pl,mon]) V.2.2
  rwa [V.1,V.2.1] at G

end RibbonD3Field
#print axioms RibbonD3Field.PowerCert.sound
