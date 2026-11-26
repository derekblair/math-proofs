import RibbonStationarySlopeCover

namespace RibbonStationaryField
open RibbonAffine (pl nf poly_eq prodP prodP_sound)
variable {K : Type*} [Field K]

inductive Leaf where
  | linear (a : Nat)
  | reject (f : Poly) (C : Reject)
  deriving Inhabited

def Leaf.poly : Leaf → Poly
  | .linear a => [(1,0,1),(0,0,-(a:Int))]
  | .reject f _ => f

def Leaf.valid (p : Nat) : Leaf → Prop
  | .linear a => p=11 ∧ (a=3 ∨ a=4 ∨ a=5 ∨ a=9)
  | .reject f C => rejectValid p f C

instance leafDecidable (p : Nat) (L : Leaf) : Decidable (L.valid p) := by
  cases L <;> unfold Leaf.valid <;> infer_instance

theorem leaf_sound (t : Kˣ) (n p : Nat) (L : Leaf) (V : L.valid p)
    (odd : Odd n) (no3 : ¬3∣n) (tn : t^n=1) (P : (p:K)=0) (F : pl t 1 L.poly=0) :
    (11:K)=0 ∧ ((t:K)=3 ∨ (t:K)=4 ∨ (t:K)=5 ∨ (t:K)=9) := by
  cases L with
  | linear a =>
    rcases V with ⟨r,v⟩
    subst p
    have e : (t:K)=(a:K) := by
      change pl t 1 [(1,0,1),(0,0,-(a:Int))]=0 at F
      simpa [pl,RibbonAffine.mon,←sub_eq_add_neg,sub_eq_zero] using F
    exact ⟨P,by rcases v with rfl|rfl|rfl|rfl <;> simp [e]⟩
  | reject f C =>
    exact False.elim (reject_sound p f C V t n odd no3 tn (by simpa using P) F)

structure ModRow where
  p : Nat
  wit : Id
  leaves : List Leaf
  deriving Inhabited

def modValid (f g h : Poly) (R : ModRow) : Prop :=
  R.wit.valid f g h R.p ∧ (R.leaves.all fun L => decide (L.valid R.p))=true ∧
    nf (prodP (R.leaves.map Leaf.poly))=nf R.wit.rhs
instance modDecidable (f g h : Poly) (R : ModRow) :
    Decidable (modValid f g h R) := by unfold modValid; infer_instance

theorem mod_sound (t : Kˣ) (n : Nat) (odd : Odd n) (no3 : ¬3∣n) (tn : t^n=1)
    (f g h : Poly) (R : ModRow) (V : modValid f g h R)
    (F : pl t 1 f=0) (G : pl t 1 g=0) (H : pl t 1 h=0) (P : (R.p:K)=0) :
    (11:K)=0 ∧ ((t:K)=3 ∨ (t:K)=4 ∨ (t:K)=5 ∨ (t:K)=9) := by
  have Y := R.wit.sound f g h R.p V.1 t F G H (by simpa using P)
  have E := poly_eq t 1 _ _ V.2.2
  rw [Y,prodP_sound] at E
  obtain ⟨v,hv,v0⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp E)
  obtain ⟨L,hL,rfl⟩ := List.mem_map.mp hv
  exact leaf_sound t n R.p L (of_decide_eq_true (List.all_eq_true.mp V.2.1 L hL))
    odd no3 tn P v0

structure PrimeCert where
  twopow : Nat
  rows : List ModRow
  deriving Inhabited

def primeValid (f : Poly) (C : CheckRow) (R : PrimeCert) : Prop :=
  C.cert.n.natAbs=2^R.twopow*(R.rows.map ModRow.p).prod ∧
    (R.rows.all fun r => decide (modValid f C.tr (binom C.e) r))=true
instance primeDecidable (f : Poly) (C : CheckRow) (R : PrimeCert) :
    Decidable (primeValid f C R) := by unfold primeValid; infer_instance

theorem prime_sound (t : Kˣ) (n : Nat) (odd : Odd n) (no3 : ¬3∣n) (tn : t^n=1)
    (two : (2:K)≠0) (f : Poly) (C : CheckRow) (R : PrimeCert) (V : primeValid f C R)
    (F : pl t 1 f=0) (G : pl t 1 C.tr=0) (H : pl t 1 (binom C.e)=0)
    (N : (C.cert.n:K)=0) :
    (11:K)=0 ∧ ((t:K)=3 ∨ (t:K)=4 ∨ (t:K)=5 ∨ (t:K)=9) := by
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
  exact mod_sound t n odd no3 tn f C.tr (binom C.e) r
    (of_decide_eq_true (List.all_eq_true.mp V.2 r hr)) F G H p0

end RibbonStationaryField
#print axioms RibbonStationaryField.prime_sound
