import RibbonD3FieldSlopeInteger
import RibbonD3FieldScalar

namespace RibbonD3Field
open RibbonAffine (Mono pl mon eRow)
variable {K : Type*} [Field K]

structure RationalPoint where
  ax : Int
  ad : Int
  bx : Int
  bd : Int
  deriving Inhabited, DecidableEq

def RationalPoint.Rep (P : RationalPoint) (a b : Kˣ) : Prop :=
  (P.ad:K)≠0 ∧ (P.bd:K)≠0 ∧
  (a:K)*(P.ad:K)=(P.ax:K) ∧ (b:K)*(P.bd:K)=(P.bx:K)

def RationalPoint.power (P : RationalPoint) (r : Nat) (i j : Int) : Int :=
  P.ax^(r+i).toNat * P.ad^(r-i).toNat *
  (P.bx^(r+j).toNat * P.bd^(r-j).toNat)

def RationalPoint.scale (P : RationalPoint) (r : Nat) : Int :=
  (P.ax*P.ad)^r * (P.bx*P.bd)^r

def RationalPoint.scaled (P : RationalPoint) (r : Nat) (L : Label) : Bool × Int × Int :=
  (L.side, P.power r L.i L.j, (L.tr.map fun m => m.2.2 * P.power r m.1 m.2.1).sum)

def Boxed (r : Nat) (i j : Int) : Prop :=
  -(r:ℤ) ≤ i ∧ i ≤ (r:ℤ) ∧ -(r:ℤ) ≤ j ∧ j ≤ (r:ℤ)
instance (r : Nat) (i j : Int) : Decidable (Boxed r i j) := by unfold Boxed; infer_instance

def BoxedLabel (r : Nat) (L : Label) : Prop :=
  Boxed r L.i L.j ∧ (L.tr.all fun m => decide (Boxed r m.1 m.2.1))=true
instance (r : Nat) (L : Label) : Decidable (BoxedLabel r L) := by unfold BoxedLabel; infer_instance

theorem rational_power_unit (x d a : Kˣ) (r : Nat) (i : Int)
    (lo : -(r:ℤ) ≤ i) (hi : i ≤ (r:ℤ)) (A : a*d=x) :
    x^(r+i).toNat * d^(r-i).toNat = ((x*d)^r)*a^i := by
  have E : a=x/d := by rw [eq_div_iff_mul_eq', A]
  have h1 : (0:ℤ) ≤ r+i := by omega
  have h2 : (0:ℤ) ≤ r-i := by omega
  rw [← zpow_natCast x, ← zpow_natCast d, Int.toNat_of_nonneg h1,Int.toNat_of_nonneg h2,
    zpow_add, zpow_sub, E, div_zpow, div_eq_mul_inv, mul_pow, zpow_natCast, zpow_natCast]
  ac_rfl

theorem RationalPoint.power_sound (P : RationalPoint) (r : Nat) (i j : Int) (X : Boxed r i j)
    (a b : Kˣ) (R : P.Rep a b) :
    (P.power r i j:K)=(P.scale r:K)* ((a^i*b^j:Kˣ):K) := by
  obtain ⟨d,e,A,B⟩ := R
  have x : (P.ax:K)≠0 := by rw [←A]; exact mul_ne_zero (Units.ne_zero a) d
  have y : (P.bx:K)≠0 := by rw [←B]; exact mul_ne_zero (Units.ne_zero b) e
  have A' : a * Units.mk0 (P.ad:K) d = Units.mk0 (P.ax:K) x := Units.ext A
  have B' : b * Units.mk0 (P.bd:K) e = Units.mk0 (P.bx:K) y := Units.ext B
  have Ah := congrArg (fun z : Kˣ => (z:K)) (rational_power_unit _ _ _ r i X.1 X.2.1 A')
  have Bh := congrArg (fun z : Kˣ => (z:K)) (rational_power_unit _ _ _ r j X.2.2.1 X.2.2.2 B')
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0] at Ah Bh
  simp only [RationalPoint.power,RationalPoint.scale,Int.cast_mul,Int.cast_pow,Units.val_mul]
  rw [Ah,Bh]
  ac_rfl

theorem RationalPoint.scaled_sound (P : RationalPoint) (r : Nat) (L : Label)
    (Z : BoxedLabel r L) (a b : Kˣ) (R : P.Rep a b) :
    let z := P.scaled r L
    let q := eRow a b L.toRow
    (z.2.1:K)=(P.scale r:K)*(q.2.1:K) ∧ (z.2.2:K)=(P.scale r:K)*q.2.2 := by
  constructor
  · exact P.power_sound r L.i L.j Z.1 a b R
  · change (((L.tr.map fun m => m.2.2 * P.power r m.1 m.2.1).sum : Int):K) =
      (P.scale r:K)*pl a b L.tr
    rw [Int.cast_list_sum]
    simp only [List.map_map,Function.comp_def,Int.cast_mul,pl,← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro m hm
    have V := of_decide_eq_true (List.all_eq_true.mp Z.2 m hm)
    rw [P.power_sound r m.1 m.2.1 V a b R]
    simp only [mon]
    ring

def GoodRatRow (P : RationalPoint) (r : Nat) (C : Chart) (p : Bool × Int × Int) (i : Fin C.reps.size) :=
  BoxedLabel r C.reps[i] ∧ p=P.scaled r C.reps[i]
instance (P : RationalPoint) (r : Nat) (C : Chart) (p : Bool × Int × Int) (i : Fin C.reps.size) :
    Decidable (GoodRatRow P r C p i) := by unfold GoodRatRow; infer_instance

def PairRat (c : Nat) (u v : Bool × Int × Int) : Prop :=
  if u.1=v.1 then Int.gcd (u.2.1-v.2.1) (u.2.2-v.2.2) ∣ c else True
instance (c : Nat) (u v : Bool × Int × Int) : Decidable (PairRat c u v) := by
  unfold PairRat; split <;> infer_instance

def RatCross (rows : Array (Bool × Int × Int)) (c : Nat) (i : Nat) : Bool :=
  (List.range rows.size).all fun j =>
    if i<j then decide (PairRat c rows[i]! rows[j]!) else true

theorem rat_cross (P : RationalPoint) (r : Nat) (C : Chart) (rows : Array (Bool × Int × Int))
    (sz : rows.size=C.reps.size)
    (R : ∀ i : Fin C.reps.size, GoodRatRow P r C rows[i.val]! i)
    (c : Nat) (test : ∀ i : Fin rows.size, RatCross rows c i.val=true)
    (a b : Kˣ) (V : P.Rep a b) (N : (c:K)≠0) : Ordered C a b := by
  intro i j lt X
  have E := List.all_eq_true.mp (test ⟨i.val, by simpa only [sz] using i.isLt⟩) j.val
    (List.mem_range.mpr (by simpa only [sz] using j.isLt))
  have H : PairRat c rows[i.val]! rows[j.val]! := of_decide_eq_true (by simpa only [lt,ite_true] using E)
  obtain ⟨bi,Pi⟩ := R i
  obtain ⟨bj,Pj⟩ := R j
  have si : rows[i.val]!.1=(eRow a b C.reps[i].toRow).1 := by rw [Pi]; rfl
  have sj : rows[j.val]!.1=(eRow a b C.reps[j].toRow).1 := by rw [Pj]; rfl
  have hside : rows[i.val]!.1=rows[j.val]!.1 := by rw [si,sj,X]
  have iS := P.scaled_sound r C.reps[i] bi a b V
  have jS := P.scaled_sound r C.reps[j] bj a b V
  rw [←Pi] at iS
  rw [←Pj,←X] at jS
  have x : (((rows[i.val]!.2.1-rows[j.val]!.2.1):ℤ):K)=0 := by
    rw [Int.cast_sub,iS.1,jS.1,sub_self]
  have y : (((rows[i.val]!.2.2-rows[j.val]!.2.2):ℤ):K)=0 := by
    rw [Int.cast_sub,iS.2,jS.2,sub_self]
  let A := rows[i.val]!.2.1-rows[j.val]!.2.1
  let B := rows[i.val]!.2.2-rows[j.val]!.2.2
  have G : (Int.gcd A B:K)=0 := by
    rw [← Int.cast_natCast, Int.gcd_eq_gcd_ab A B]
    simp only [Int.cast_add,Int.cast_mul,show (A:K)=0 from x,show (B:K)=0 from y,zero_mul,add_zero]
  have Div : Int.gcd A B ∣ c := by simpa only [PairRat,hside,ite_true] using H
  obtain ⟨w,T⟩ := Div
  apply N
  rw [T,Nat.cast_mul,G,zero_mul]

#print axioms RibbonD3Field.rat_cross
end RibbonD3Field
