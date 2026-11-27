import RibbonD3InvertCore
import RibbonD3WideScalar

namespace RibbonD3Wide
open RibbonD3Field
variable {K : Type*} [Field K]

inductive RatReason
  | factor (slot : Fin 4)
  | pivot
  | order (side : Bool) (u v m : Nat)
  | bad
  deriving Inhabited

structure RatPrime where
  p : Nat
  digits : Nat × Nat
  reason : RatReason
  deriving Inhabited


def orderTest (p z u v m : Nat) : Prop :=
  v=0 ∧ p-1=m*2^u ∧ (z^(p-1) : ZMod p)=1 ∧ (z^m : ZMod p)≠1
instance rationalOrderTestDecidable (p z u v m : Nat) : Decidable (orderTest p z u v m) := by unfold orderTest; infer_instance

def RatPrime.valid (P : RationalPoint) (C : RatPrime) : Prop :=
  C.p.Prime ∧ match C.reason with
  | .factor i => zeroTest C.p (P.factor i)
  | .pivot => P.Reduce C.p 1 C.digits.2
  | .order s u v m => P.Reduce C.p C.digits.1 C.digits.2 ∧
      orderTest C.p (if s then C.digits.2 else C.digits.1) u v m
  | .bad => P.Reduce C.p C.digits.1 C.digits.2 ∧
      (C.p,C.digits.1,C.digits.2)∈provisional
instance rationalPrimeValidDecidable (P : RationalPoint) (C : RatPrime) : Decidable (C.valid P) := by
  unfold RatPrime.valid
  split <;> infer_instance

theorem drop_mod_order (p z u v m : Nat) (Pr : p.Prime) (Z : (p:K)=0)
    (T : orderTest p z u v m) (a : Kˣ) (A : (a:K)=(z:K))
    (n : Nat) (odd : Odd n) (an : a^n=1) : False := by
  letI : Fact p.Prime := ⟨Pr⟩
  letI : CharP K p := (CharP.charP_iff_prime_eq_zero (R:=K) Pr).mpr Z
  let f : ZMod p→+*K := ZMod.castHom (dvd_refl p) K
  have fPow (d : Nat) : f ((z^(d:Nat):ZMod p)) = ((a^d:Kˣ):K) := by
    push_cast
    simp [A]
  have P : a^(p-1)=1 := by
    apply Units.ext
    rw [← fPow, T.2.2.1, map_one]
    rfl
  have D : ((p-1:Nat) : Int).natAbs=m*2^u := by simpa only [Int.natAbs_natCast] using T.2.1
  have Q : a^m=1 := drop_two a n odd an _ m u D (by simpa using P)
  apply T.2.2.2
  apply f.injective
  rw [fPow,Q,map_one]
  rfl

theorem RatPrime.sound (P : RationalPoint) (C : RatPrime) (V : C.valid P)
    (a b : Kˣ) (R : P.Rep a b) (n : Nat) (odd : Odd n)
    (an : a^n=1) (bn : b^n=1) (a1 : a≠1) (Z : (C.p:K)=0) :
    ∃ p x y : Nat, p.Prime ∧ (p:K)=0 ∧ (a:K)=(x:K) ∧ (b:K)=(y:K) ∧ (p,x,y)∈provisional := by
  obtain ⟨Pr,V⟩ := V
  cases H : C.reason with
  | factor i =>
    rw [H] at V
    have Y := zeroTest_sound V Z
    obtain ⟨ad,bd,A,B⟩ := R
    have ax := mul_ne_zero (Units.ne_zero a) ad
    have bx := mul_ne_zero (Units.ne_zero b) bd
    rw [A] at ax
    rw [B] at bx
    fin_cases i
    · exact False.elim (ax Y)
    · exact False.elim (ad Y)
    · exact False.elim (bx Y)
    · exact False.elim (bd Y)
  | pivot =>
    rw [H] at V
    exact False.elim (a1 (Units.ext (by simpa using (P.reduce_cast a b R C.p 1 C.digits.2 V Z).1)))
  | order side u v m =>
    rw [H] at V
    obtain ⟨A,B⟩ := P.reduce_cast a b R C.p _ _ V.1 Z
    cases side
    · exact False.elim (drop_mod_order C.p C.digits.1 u v m Pr Z V.2 a A n odd an)
    · exact False.elim (drop_mod_order C.p C.digits.2 u v m Pr Z V.2 b B n odd bn)
  | bad =>
    rw [H] at V
    obtain ⟨A,B⟩ := P.reduce_cast a b R C.p _ _ V.1 Z
    exact ⟨C.p,_,_,Pr,Z,A,B,V.2⟩

structure TriReceipt where
  strip : Nat × Nat
  primes : List Nat
  mods : List RatPrime
  deriving Inhabited

def TriReceipt.valid (c d e : Int) (Z : TriReceipt) : Prop :=
  (triValue c d e).natAbs=2^Z.strip.1*3^Z.strip.2*Z.primes.prod ∧
    (Z.primes.all fun p => decide (∃ i : Fin Z.mods.length, Z.mods[i].p=p ∧ Z.mods[i].valid (triPoint c d)))=true
instance wideTriReceiptValidDecidable (c d e : Int) (Z : TriReceipt) : Decidable (Z.valid c d e) := by
  unfold TriReceipt.valid; infer_instance

theorem TriReceipt.sound (c d e : Int) (Z : TriReceipt) (V : Z.valid c d e)
    (a b : Kˣ) (n : Nat) (odd : Odd n) (two : (2:K)≠0) (three : (3:K)≠0)
    (an : a^n=1) (bn : b^n=1) (a1 : a≠1)
    (R : (triPoint c d).Rep a b) (E : (triValue c d e:K)=0) :
    ∃ p x y : Nat, p.Prime ∧ (p:K)=0 ∧ (a:K)=(x:K) ∧ (b:K)=(y:K) ∧ (p,x,y)∈provisional := by
  obtain ⟨p,P,X⟩ := int_zero_primes _ _ _ _ V.1 two three E
  obtain ⟨i,HP,VP⟩ := of_decide_eq_true (List.all_eq_true.mp V.2 p P)
  exact Z.mods[i].sound (triPoint c d) VP a b R n odd an bn a1 (by rwa [HP])

end RibbonD3Wide
#print axioms RibbonD3Wide.TriReceipt.sound
