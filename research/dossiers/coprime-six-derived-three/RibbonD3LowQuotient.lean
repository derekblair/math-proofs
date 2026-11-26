import RibbonD3VertexMates
import RibbonD3FieldCharts

namespace RibbonD3Low
open RibbonD3VertexMates RibbonD3WordSelection Ribbon5Bridge
open HaarClass4Structure HaarClass4Ports RibbonClass4Fallback
open scoped commutatorElement
variable {G : Type*} [Group G]

def low (k : Count) (i : Nat) : Q :=
  (block k i).foldl push (false,0,0,0)

def lowKey (p : Nat) (q : Q) : Bool × ℤ × ℤ × ℤ :=
  (q.1,q.2.1,q.2.2.1,q.2.2.2 % (p : ℤ))

def smallGaps (p : Nat) (k : Count) (i j : Nat) : Prop :=
  ((low k i).2.1-(low k j).2.1).natAbs < p ∧
    ((low k i).2.2.1-(low k j).2.2.1).natAbs < p
instance (p : Nat) (k : Count) (i j : Nat) : Decidable (smallGaps p k i j) := by
  unfold smallGaps
  infer_instance

theorem run_collect (x y c : G) (cx : Commute c x) (cy : Commute c y)
    (xy : x*y=y*x*c) (q : Q) (w : List P) :
    vert x y c (w.foldl push q) = run x y (vert x y c q) w := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih =>
    change vert x y c (w.foldl push (push q a)) =
      run x y (action x y (vert x y c q) a) w
    rw [ih,move x y c cx cy xy]

private theorem order_dvd_abs (c : G) {i j : ℤ} (eq : c^i=c^j) :
    orderOf c∣(i-j).natAbs := by
  have E : c^(i-j)=1 := by rw [zpow_sub,eq,mul_inv_cancel]
  apply orderOf_dvd_iff_pow_eq_one.mpr
  by_cases h : 0 ≤ i - j
  · rw [←zpow_natCast,Int.natAbs_of_nonneg h]
    exact E
  · rw [←zpow_natCast,Int.ofNat_natAbs_of_nonpos (by omega : i-j≤0),
       zpow_neg,E,inv_one]

private theorem order_dvd_int (c : G) {i j : ℤ} (eq : c^i=c^j) :
    (orderOf c : Int) ∣ (i-j) := by
  exact Int.natCast_dvd.mpr (order_dvd_abs c eq)

private theorem eq_of_zpow {p : Nat} (x : G) (o : orderOf x = p) {i j : Int}
    (h : (i-j).natAbs < p) (e : x^i=x^j) : i=j := by
  have hₘ := order_dvd_abs x e
  rw [o] at hₘ
  by_contra N
  have P : 0 < (i-j).natAbs := by omega
  exact (Nat.not_le_of_gt h) (Nat.le_of_dvd P hₘ)

theorem lowKey_eq (x y : G) (k : Count) {p i j : Nat}
    (O : orderOf (QuotientGroup.mk' (LS G 2) (portC x y)) = p)
    (S : smallGaps p k i j) (E : vertex x y k i = vertex x y k j) :
    lowKey p (low k i) = lowKey p (low k j) := by
  let f := QuotientGroup.mk' (LS G 2)
  let c := f (portC x y)
  have U : f (portU x y)=1 := (QuotientGroup.eq_one_iff _).mpr (layer_u x y)
  have V : f (portV x y)=1 := (QuotientGroup.eq_one_iff _).mpr (layer_v x y)
  have cx : Commute c (f x) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [c, portU,map_commutatorElement] using U
  have cy : Commute c (f y) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [c, portV,map_commutatorElement] using V
  have xy : f x*f y=f y*f x*c := by simpa only [c,map_mul] using congrArg f (ports_xy x y)
  have P (a : Nat) : ((vertex x y k a).1, f (vertex x y k a).2) =
      vert (f x) (f y) c (low k a) := by
    have Q := mapped_run f x y (start G) (block k a)
    have R := run_collect (f x) (f y) c cx cy xy (false,0,0,0) (block k a)
    have Z : vert (f x) (f y) c (false,0,0,0) = (false,1) := by
      simp only [vert,HaarCycle.norm,zpow_zero,one_mul]
    rw [Z] at R
    change ((vertex x y k a).1, f (vertex x y k a).2) =
      run (f x) (f y) (false,f 1) (block k a) at Q
    rw [map_one] at Q
    exact Q.trans R.symm
  have K := (P i).symm.trans ((congrArg (fun z : Bool×G => (z.1,f z.2)) E).trans (P j))
  have V2 : HaarCycle.norm (f x) (f y) c (low k i).2 =
      HaarCycle.norm (f x) (f y) c (low k j).2 := congrArg Prod.snd K
  have M := HaarBound16.conjugate_eq (f x) (f y) c cx cy xy V2
  have loI := eq_of_zpow c O S.1 M.1
  have loJ := eq_of_zpow c O S.2 M.2
  unfold HaarCycle.norm at V2
  rw [loI,loJ] at V2
  have D := order_dvd_int c (mul_left_cancel V2)
  change orderOf c = p at O
  rw [O] at D
  have modEq : (low k i).2.2.2 % (p : ℤ) = (low k j).2.2.2 % (p : ℤ) :=
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd D)
  have se : (low k i).1 = (low k j).1 := congrArg (Prod.fst : Bool × (G ⧸ LS G 2) → Bool) K
  simp only [lowKey,se,loI,loJ,modEq]

#print axioms lowKey_eq
end RibbonD3Low
