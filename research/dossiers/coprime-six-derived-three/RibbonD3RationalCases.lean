import RibbonD3RationalCore
import RibbonD3FieldDirect

namespace RibbonD3Field
open RibbonStationaryField (coprime_drop)
variable {K : Type*} [Field K]

def zeroTest (p : Nat) (x : Int) : Prop := (p:ℤ) ∣ x
instance rationalZeroTestDecidable (p : Nat) (x : Int) : Decidable (zeroTest p x) := by unfold zeroTest; infer_instance

theorem zeroTest_sound {p : Nat} {x : Int} (T : zeroTest p x) (P : (p:K)=0) : (x:K)=0 := by
  obtain ⟨w,H⟩ := T
  rw [H,Int.cast_mul,Int.cast_natCast,P,zero_mul]

def RationalPoint.Reduce (P : RationalPoint) (p x y : Nat) : Prop :=
  zeroTest p (P.ax-(x:ℤ)*P.ad) ∧ zeroTest p (P.bx-(y:ℤ)*P.bd)
instance rationalReduceDecidable (P : RationalPoint) (p x y : Nat) : Decidable (P.Reduce p x y) := by
  unfold RationalPoint.Reduce; infer_instance

theorem RationalPoint.reduce_cast (P : RationalPoint) (a b : Kˣ) (R : P.Rep a b)
    (p x y : Nat) (H : P.Reduce p x y) (Q : (p:K)=0) :
    (a:K)=(x:K) ∧ (b:K)=(y:K) := by
  obtain ⟨hd,he,A,B⟩ := R
  obtain ⟨ha,hb⟩ := H
  have X := zeroTest_sound ha Q
  have Y := zeroTest_sound hb Q
  simp only [Int.cast_sub,Int.cast_mul,Int.cast_natCast,← A,← B,sub_eq_zero] at X Y
  exact ⟨mul_right_cancel₀ hd X,mul_right_cancel₀ he Y⟩

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

def RationalPoint.factor (P : RationalPoint) (i : Fin 4) : Int := ![P.ax,P.ad,P.bx,P.bd] i

def orderTest (p z u v m : Nat) : Prop :=
  p-1=m*(2^u*3^v) ∧ (z^(p-1) : ZMod p)=1 ∧ (z^m : ZMod p)≠1
instance rationalOrderTestDecidable (p z u v m : Nat) : Decidable (orderTest p z u v m) := by unfold orderTest; infer_instance

def RatPrime.valid (P : RationalPoint) (C : RatPrime) : Prop :=
  C.p.Prime ∧ match C.reason with
  | .factor i => zeroTest C.p (P.factor i)
  | .pivot => P.Reduce C.p 1 C.digits.2
  | .order s u v m => P.Reduce C.p C.digits.1 C.digits.2 ∧
      orderTest C.p (if s then C.digits.2 else C.digits.1) u v m
  | .bad => P.Reduce C.p C.digits.1 C.digits.2 ∧
      (C.p,C.digits.1,C.digits.2)∈exactBad
instance rationalPrimeValidDecidable (P : RationalPoint) (C : RatPrime) : Decidable (C.valid P) := by
  unfold RatPrime.valid
  split <;> infer_instance

theorem drop_mod_order (p z u v m : Nat) (Pr : p.Prime) (Z : (p:K)=0)
    (T : orderTest p z u v m) (a : Kˣ) (A : (a:K)=(z:K))
    (n : Nat) (odd : Odd n) (no3 : ¬3∣n) (an : a^n=1) : False := by
  letI : Fact p.Prime := ⟨Pr⟩
  letI : CharP K p := (CharP.charP_iff_prime_eq_zero (R:=K) Pr).mpr Z
  let f : ZMod p→+*K := ZMod.castHom (dvd_refl p) K
  have fPow (d : Nat) : f ((z^(d:Nat):ZMod p)) = ((a^d:Kˣ):K) := by
    push_cast
    simp [A]
  have P : a^(p-1)=1 := by
    apply Units.ext
    rw [← fPow, T.2.1, map_one]
    rfl
  have D : ((p-1:Nat) : Int).natAbs=m*(2^u*3^v) := by simpa only [Int.natAbs_natCast] using T.1
  have Q : a^m=1 := coprime_drop n odd no3 a an _ m u v D (by simpa using P)
  apply T.2.2
  apply f.injective
  rw [fPow,Q,map_one]
  rfl

theorem RatPrime.sound (P : RationalPoint) (C : RatPrime) (V : C.valid P)
    (a b : Kˣ) (R : P.Rep a b) (n : Nat) (odd : Odd n) (no3 : ¬3∣n)
    (an : a^n=1) (bn : b^n=1) (a1 : a≠1) (Z : (C.p:K)=0) :
    ∃ p x y : Nat, p.Prime ∧ (p:K)=0 ∧ (a:K)=(x:K) ∧ (b:K)=(y:K) ∧ (p,x,y)∈exactBad := by
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
    · exact False.elim (drop_mod_order C.p C.digits.1 u v m Pr Z V.2 a A n odd no3 an)
    · exact False.elim (drop_mod_order C.p C.digits.2 u v m Pr Z V.2 b B n odd no3 bn)
  | bad =>
    rw [H] at V
    obtain ⟨A,B⟩ := P.reduce_cast a b R C.p _ _ V.1 Z
    exact ⟨C.p,_,_,Pr,Z,A,B,V.2⟩

structure RatioBank where
  chartIdx : Count
  point : RationalPoint
  rangeBound : Nat
  rows : Array (Bool × Int × Int)
  constant : Nat
  strip : Nat × Nat
  factors : List (Nat × Nat)
  mods : List RatPrime
  deriving Inhabited

def RatioBank.factorValid (C : RatioBank) : Prop :=
  C.constant=2^C.strip.1*3^C.strip.2*(C.factors.map fun x => x.1^x.2).prod ∧
    (C.factors.all fun pe => decide (∃ i : Fin C.mods.length, C.mods[i].p=pe.1 ∧ C.mods[i].valid C.point))=true
instance rationalRatioBankFactorDecidable (C : RatioBank) : Decidable C.factorValid := by unfold RatioBank.factorValid; infer_instance

theorem RatioBank.sound (C : RatioBank) (F : C.factorValid) (sz : C.rows.size=(chart C.chartIdx).reps.size)
    (R : ∀ i : Fin (chart C.chartIdx).reps.size, GoodRatRow C.point C.rangeBound (chart C.chartIdx) C.rows[i.val]! i)
    (T : ∀ i : Fin C.rows.size, RatCross C.rows C.constant i.val=true)
    (a b : Kˣ) (V : C.point.Rep a b) (n : Nat) (odd : Odd n) (no3 : ¬3∣n)
    (an : a^n=1) (bn : b^n=1) (a1 : a≠1) (two : (2:K)≠0) (three : (3:K)≠0) :
    (∃ k : Count, Ordered (chart k) a b) ∨
      ∃ p x y : Nat, p.Prime ∧ (p:K)=0 ∧ (a:K)=(x:K) ∧ (b:K)=(y:K) ∧ (p,x,y)∈exactBad := by
  by_cases h : (C.constant:K)=0
  · right
    rw [F.1,Nat.cast_mul,Nat.cast_mul,Nat.cast_pow,Nat.cast_pow] at h
    have Q := (mul_eq_zero.mp h).resolve_left
      (mul_ne_zero (pow_ne_zero _ (by simpa using two)) (pow_ne_zero _ (by simpa using three)))
    rw [Nat.cast_list_prod,List.map_map] at Q
    obtain ⟨x,W,N⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp Q)
    have Z : (x.1:K)=0 := by
      exact ((pow_eq_zero_iff').mp (by simpa only [Nat.cast_pow] using (show ((x.1^x.2:Nat):K)=0 from N))).1
    obtain ⟨i,HP,M⟩ := of_decide_eq_true (List.all_eq_true.mp F.2 x W)
    exact C.mods[i].sound C.point M a b V n odd no3 an bn a1 (by rwa [HP])
  · exact Or.inl ⟨C.chartIdx,rat_cross C.point C.rangeBound (chart C.chartIdx) C.rows sz R C.constant T a b V h⟩

def ratioChunk (n : Nat) (check : Nat → Bool) (b : Fin 16) : Bool :=
  (List.range 8).all fun i => if 8*b.val+i<n then check (8*b.val+i) else true

theorem ratioChunk_sound (n : Nat) (bound : n≤128) (check : Nat → Bool)
    (H : ∀ b : Fin 16, ratioChunk n check b=true) (i : Fin n) : check i.val=true := by
  have hd := i.isLt
  let b : Fin 16 := ⟨i.val/8,by omega⟩
  have e : 8*b.val+i.val%8=i.val := by dsimp [b]; omega
  have V := List.all_eq_true.mp (H b) (i.val%8) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  simpa only [e,hd,ite_true] using V

def ratioRowsCheck (C : RatioBank) (i : Nat) : Bool :=
  if h : i<(chart C.chartIdx).reps.size then
    decide (GoodRatRow C.point C.rangeBound (chart C.chartIdx) C.rows[i]! ⟨i,h⟩)
  else true

theorem rationalRowsByChunks (C : RatioBank) (bound : (chart C.chartIdx).reps.size≤128)
    (H : ∀ b : Fin 16, ratioChunk (chart C.chartIdx).reps.size (ratioRowsCheck C) b=true)
    (i : Fin (chart C.chartIdx).reps.size) :
    GoodRatRow C.point C.rangeBound (chart C.chartIdx) C.rows[i.val]! i := by
  have T := ratioChunk_sound _ bound _ H i
  exact of_decide_eq_true (by simpa only [ratioRowsCheck,i.isLt,dif_pos,Fin.eta] using T)

theorem rationalCrossByChunks (C : RatioBank) (bound : C.rows.size≤128)
    (H : ∀ b : Fin 16, ratioChunk C.rows.size (RatCross C.rows C.constant) b=true)
    (i : Fin C.rows.size) : RatCross C.rows C.constant i.val=true :=
  ratioChunk_sound _ bound _ H i

#print axioms RibbonD3Field.RatioBank.sound
end RibbonD3Field
