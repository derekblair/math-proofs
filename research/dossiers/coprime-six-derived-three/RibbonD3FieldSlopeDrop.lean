import RibbonD3FieldPower
import RibbonD3FieldSlopeInteger

namespace RibbonD3Field
open RibbonStationaryField (Id Poly natConst coprime_drop)
open RibbonAffine (pl mon negative negative_sound pl_append)
variable {K : Type*} [Field K]

def tVar : Poly := [(1,0,1)]
def minusOne (f : Poly) : Poly := f++[(0,0,-1)]

theorem tVar_eval (t : Kˣ) : pl t 1 tVar = (t:K) := by simp [tVar,pl,mon]
theorem constOne_eval (t : Kˣ) : pl t 1 (natConst 1) = 1 := by simp [natConst,pl,mon]
theorem minusOne_eval (t : Kˣ) (f : Poly) : pl t 1 (minusOne f)=pl t 1 f-1 := by
  simp [minusOne,pl_append,pl,mon,sub_eq_add_neg]

inductive Exclude where
  | zero
  | notPivot (pow : PowerCert)
  | oddPower (e d u v : Nat) (r : Poly) (one two : PowerCert) (empty : Id)
  deriving Inhabited

def Exclude.valid (p : Nat) (f : Poly) (v : Int) : Exclude → Prop
  | .zero => f=tVar
  | .notPivot A => A.ok p f tVar v.natAbs (natConst 1)
  | .oddPower e d u v r A B E => e=d*(2^u*3^v) ∧ A.ok p f tVar e (natConst 1) ∧
      B.ok p f tVar d r ∧ E.rhs=natConst 1 ∧ E.valid f (minusOne r) [] p

instance (p : Nat) (f : Poly) (v : Int) (D : Exclude) : Decidable (D.valid p f v) := by
  cases D <;> unfold Exclude.valid <;> infer_instance

theorem exclude (p : Nat) (f : Poly) (v : Int) (D : Exclude) (V : D.valid p f v)
    (t : Kˣ) (n : Nat) (odd : Odd n) (no3 : ¬3∣n) (tn : t^n=1) (pivot : t^v≠1)
    (P : (p:K)=0) (F : pl t 1 f=0) : False := by
  have p0 : ((p:Int):K)=0 := by simpa using P
  cases D with
  | zero =>
    have E : f=tVar := V
    rw [E,tVar_eval] at F
    exact Units.ne_zero _ F
  | notPivot A =>
    have H := A.sound p f tVar v.natAbs (natConst 1) V t p0 F
    rw [tVar_eval,constOne_eval] at H
    have E : t^v.natAbs=1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val,Units.val_one]
      exact H.symm
    have d := orderOf_dvd_iff_pow_eq_one.mpr E
    apply pivot
    exact orderOf_dvd_iff_zpow_eq_one.mp (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr d))
  | oddPower e d x y r A B E =>
    obtain ⟨eq,U,W,X,Z⟩ := V
    have H := A.sound p f tVar e (natConst 1) U t p0 F
    rw [tVar_eval,constOne_eval] at H
    have Hd : t^e=1 := by apply Units.ext; simpa only [Units.val_pow_eq_pow_val,Units.val_one] using H.symm
    have P' := coprime_drop n odd no3 t tn (e:Int) d x y (by simpa using eq) (by simpa using Hd)
    have Q := B.sound p f tVar d r W t p0 F
    rw [tVar_eval,←Units.val_pow_eq_pow_val,P',Units.val_one] at Q
    have Q' : pl t 1 (minusOne r)=0 := by simp [minusOne_eval,Q]
    have I := E.sound f (minusOne r) [] p Z t F Q' rfl p0
    rw [X,constOne_eval] at I
    exact (one_ne_zero : (1:K)≠0) I

/-- Exact scalar reduction: accepted roots are degree one after all field exclusions. -/
def rootPoly (s : Nat) : Poly := [(1,0,1),(0,0,-(s:Int))]

theorem linear_root (s : Nat) (t : Kˣ) (F : pl t 1 (rootPoly s)=0) : (t:K)=(s:K) := by
  simpa [rootPoly,pl,mon,←sub_eq_add_neg,sub_eq_zero] using F

end RibbonD3Field
#print axioms RibbonD3Field.exclude
