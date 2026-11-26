import RibbonAllOddSlopeCover

namespace RibbonAllOddField
open RibbonAffine (pl nf poly_eq prodP prodP_sound)
open RibbonStationaryField (Branch Poly Id binom)
def AllowedRoot (B : Branch) (p a : Nat) : Prop :=
  (p=7 ∧ (a=2 ∨ a=4)) ∨ (p=11 ∧ (a=3 ∨ a=4 ∨ a=5 ∨ a=9)) ∨
  (p=13 ∧ (a=3 ∨ a=9)) ∨ (p=43 ∧ a=31 ∧ B.u=0 ∧ B.v=1)

instance (B : Branch) (p a : Nat) : Decidable (AllowedRoot B p a) := by
  unfold AllowedRoot
  infer_instance

variable {K : Type*} [Field K]

inductive Leaf where
  | linear (p a : Nat)
  | reject (f : Poly) (C : Reject)
  deriving Inhabited

def Leaf.poly : Leaf → Poly
  | .linear _ a => [(1,0,1),(0,0,-(a:Int))]
  | .reject f _ => f

def Leaf.valid (B : Branch) (p : Nat) : Leaf → Prop
  | .linear q a => p=q ∧ AllowedRoot B p a
  | .reject f C => rejectValid p f C

instance leafDecidable (B : Branch) (p : Nat) (L : Leaf) : Decidable (L.valid B p) := by
  cases L <;> unfold Leaf.valid <;> infer_instance

def ResidueRoot (B : Branch) (t : Kˣ) : Prop :=
  ∃ p a : Nat, (p:K)=0 ∧ (t:K)=(a:K) ∧ AllowedRoot B p a

theorem leaf_sound (B : Branch) (t : Kˣ) (n p : Nat) (L : Leaf) (V : L.valid B p)
    (odd : Odd n) (tn : t^n=1) (P : (p:K)=0) (F : pl t 1 L.poly=0) :
    ResidueRoot B t := by
  cases L with
  | linear q a =>
    rcases V with ⟨r,v⟩
    subst q
    have e : (t:K)=(a:K) := by
      change pl t 1 [(1,0,1),(0,0,-(a:Int))]=0 at F
      simpa [pl,RibbonAffine.mon,←sub_eq_add_neg,sub_eq_zero] using F
    exact ⟨p,a,P,e,v⟩
  | reject f C =>
    exact False.elim (reject_sound p f C V t n odd tn (by simpa using P) F)

structure ModRow where
  p : Nat
  wit : Id
  leaves : List Leaf
  deriving Inhabited

def modValid (B : Branch) (g h : Poly) (R : ModRow) : Prop :=
  R.wit.valid B.p g h R.p ∧ (R.leaves.all fun L => decide (L.valid B R.p))=true ∧
    nf (prodP (R.leaves.map Leaf.poly))=nf R.wit.rhs
instance modDecidable (B : Branch) (g h : Poly) (R : ModRow) :
    Decidable (modValid B g h R) := by unfold modValid; infer_instance

theorem mod_sound (t : Kˣ) (n : Nat) (odd : Odd n) (tn : t^n=1)
    (B : Branch) (g h : Poly) (R : ModRow) (V : modValid B g h R)
    (F : pl t 1 B.p=0) (G : pl t 1 g=0) (H : pl t 1 h=0) (P : (R.p:K)=0) :
    ResidueRoot B t := by
  have Y := R.wit.sound B.p g h R.p V.1 t F G H (by simpa using P)
  have E := poly_eq t 1 _ _ V.2.2
  rw [Y,prodP_sound] at E
  obtain ⟨v,hv,v0⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp E)
  obtain ⟨L,hL,rfl⟩ := List.mem_map.mp hv
  exact leaf_sound B t n R.p L (of_decide_eq_true (List.all_eq_true.mp V.2.1 L hL))
    odd tn P v0

structure PrimeCert where
  twopow : Nat
  rows : List ModRow
  deriving Inhabited

def primeValid (B : Branch) (C : CheckRow) (R : PrimeCert) : Prop :=
  C.cert.n.natAbs=2^R.twopow*(R.rows.map ModRow.p).prod ∧
    (R.rows.all fun r => decide (modValid B C.tr (binom C.e) r))=true
instance primeDecidable (B : Branch) (C : CheckRow) (R : PrimeCert) :
    Decidable (primeValid B C R) := by unfold primeValid; infer_instance

theorem prime_sound (t : Kˣ) (n : Nat) (odd : Odd n) (tn : t^n=1)
    (two : (2:K)≠0) (B : Branch) (C : CheckRow) (R : PrimeCert) (V : primeValid B C R)
    (F : pl t 1 B.p=0) (G : pl t 1 C.tr=0) (H : pl t 1 (binom C.e)=0)
    (N : (C.cert.n:K)=0) :
    ResidueRoot B t := by
  have Y : (C.cert.n.natAbs:K)=0 := by
    by_cases p : 0≤C.cert.n
    · rw [←Int.cast_natCast,Int.natAbs_of_nonneg p]
      exact N
    · rw [← Int.cast_natCast, show (C.cert.n.natAbs:Int) = -C.cert.n by omega,Int.cast_neg,N,neg_zero]
  rw [V.1,Nat.cast_mul,Nat.cast_pow] at Y
  have P : (((R.rows.map ModRow.p).prod:Nat):K)=0 :=
    (mul_eq_zero.mp Y).resolve_left (pow_ne_zero _ (by simpa using two))
  rw [Nat.cast_list_prod] at P
  obtain ⟨p,hp,p0⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp P)
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
  exact mod_sound t n odd tn B C.tr (binom C.e) r
    (of_decide_eq_true (List.all_eq_true.mp V.2 r hr)) F G H p0

end RibbonAllOddField
#print axioms RibbonAllOddField.prime_sound
