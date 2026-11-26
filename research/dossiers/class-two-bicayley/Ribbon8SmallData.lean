import Ribbon8SmallCollect

namespace Ribbon8Small
open Ribbon5Bridge HaarClass3Table HaarClass3Collector64 HaarClass4Ports HaarClass4Structure
open HaarClass3Separation64 (eval)
variable {G : Type*} [Group G]

set_option maxRecDepth 30000
set_option maxHeartbeats 0

def w0 : Array P := #[0,2,1,2,1,2,1,2,1,2,0,0,2,0,2,1,2,0,2,0,2,1,1,2,1,1,2,0,2,0,0,2,0,2,1,2,1,2,0,2,1,2,1,1,2,0,2,0,2,0,2,0,2,1,2,1,1,2,1,2,0,0,2,0,0,2,1,2,1,2,0,2,1,2,1,1,2,0,2,0,2,0,2,0,2,1,1,2,1,1,2,0,2,0,0,2,0,2,1,2,1,2,1,2,1,2,0,0,2,0,2,1,2,0,2,0,2,1,2,1,1,2,1,2,0,0,2,0]
def t0 : Array State := #[(false,0,0,0,0,0),(false,1,0,0,0,0),(true,1,0,0,0,0),(true,1,-1,-1,0,1),(false,1,-1,-1,0,1),(false,0,-1,-1,1,1),(true,0,-1,-1,1,1),(true,0,-2,-1,1,2),(false,0,-2,-1,1,2),(false,-1,-2,-1,2,2),(true,-1,-2,-1,2,2),(true,-1,-1,-2,3,1),(true,-1,0,-3,4,-1),(false,-1,0,-3,4,-1),(false,0,0,-3,1,-1),(true,0,0,-3,1,-1),(true,0,-1,-3,1,2),(false,0,-1,-3,1,2),(false,1,-1,-3,-2,2),(true,1,-1,-3,-2,2),(true,1,0,-2,-2,-1),(false,1,0,-2,-2,-1),(false,0,0,-2,0,-1),(false,-1,0,-2,2,-1),(true,-1,0,-2,2,-1),(true,-1,-1,-1,1,0),(true,-1,-2,0,0,0),(false,-1,-2,0,0,0),(false,0,-2,0,0,0),(true,0,-2,0,0,0),(true,0,-1,0,0,0),(true,0,0,0,0,0),(false,0,0,0,0,0),(false,1,0,0,0,0),(true,1,0,0,0,0),(true,1,-1,-1,0,1),(false,1,-1,-1,0,1),(false,0,-1,-1,1,1),(true,0,-1,-1,1,1),(true,0,0,-1,1,0),(false,0,0,-1,1,0),(false,-1,0,-1,2,0),(true,-1,0,-1,2,0),(true,-1,-1,0,1,0),(true,-1,-2,1,0,-1),(false,-1,-2,1,0,-1),(false,0,-2,1,1,-1),(true,0,-2,1,1,-1),(true,0,-1,1,1,0),(false,0,-1,1,1,0),(false,1,-1,1,2,0),(true,1,-1,1,2,0),(true,1,0,2,2,1),(false,1,0,2,2,1),(false,0,0,2,0,1),(true,0,0,2,0,1),(true,0,-1,2,0,-1),(true,0,-2,2,0,-3),(false,0,-2,2,0,-3),(false,-1,-2,2,-2,-3),(true,-1,-2,2,-2,-3),(true,-1,-1,1,-1,-1),(true,-1,0,0,0,0),(false,-1,0,0,0,0),(false,0,0,0,0,0),(false,1,0,0,0,0),(true,1,0,0,0,0),(true,1,-1,-1,0,1),(false,1,-1,-1,0,1),(false,0,-1,-1,1,1),(true,0,-1,-1,1,1),(true,0,0,-1,1,0),(false,0,0,-1,1,0),(false,-1,0,-1,2,0),(true,-1,0,-1,2,0),(true,-1,-1,0,1,0),(true,-1,-2,1,0,-1),(false,-1,-2,1,0,-1),(false,0,-2,1,1,-1),(true,0,-2,1,1,-1),(true,0,-1,1,1,0),(false,0,-1,1,1,0),(false,1,-1,1,2,0),(true,1,-1,1,2,0),(true,1,0,2,2,1),(false,1,0,2,2,1),(false,0,0,2,0,1),(false,-1,0,2,-2,1),(true,-1,0,2,-2,1),(true,-1,-1,3,-3,-2),(true,-1,-2,4,-4,-6),(false,-1,-2,4,-4,-6),(false,0,-2,4,0,-6),(true,0,-2,4,0,-6),(true,0,-1,4,0,-2),(true,0,0,4,0,2),(false,0,0,4,0,2),(false,1,0,4,4,2),(true,1,0,4,4,2),(true,1,-1,3,4,-1),(false,1,-1,3,4,-1),(false,0,-1,3,1,-1),(true,0,-1,3,1,-1),(true,0,-2,3,1,-4),(false,0,-2,3,1,-4),(false,-1,-2,3,-2,-4),(true,-1,-2,3,-2,-4),(true,-1,-1,2,-1,-1),(true,-1,0,1,0,1),(false,-1,0,1,0,1),(false,0,0,1,1,1),(true,0,0,1,1,1),(true,0,-1,1,1,0),(false,0,-1,1,1,0),(false,1,-1,1,2,0),(true,1,-1,1,2,0),(true,1,0,2,2,1),(false,1,0,2,2,1),(false,0,0,2,0,1),(true,0,0,2,0,1),(true,0,-1,2,0,-1),(true,0,-2,2,0,-3),(false,0,-2,2,0,-3),(false,-1,-2,2,-2,-3),(true,-1,-2,2,-2,-3),(true,-1,-1,1,-1,-1),(true,-1,0,0,0,0),(false,-1,0,0,0,0),(false,0,0,0,0,0)]
def w1 : Array P := #[1,2,0,2,0,2,0,2,0,2,1,1,2,1,2,0,2,1,2,1,2,0,0,2,0,0,2,1,2,1,1,2,1,2,0,2,0,2,1,2,0,2,0,0,2,1,2,1,2,1,2,1,2,0,2,0,0,2,0,2,1,1,2,1,1,2,0,2,0,2,1,2,0,2,0,0,2,1,2,1,2,1,2,1,2,0,0,2,0,0,2,1,2,1,1,2,1,2,0,2,0,2,0,2,0,2,1,1,2,1,2,0,2,1,2,1,2,0,2,0,0,2,0,2,1,1,2,1]
def t1 : Array State := #[(false,0,0,0,0,0),(false,-1,0,0,0,0),(true,-1,0,0,0,0),(true,-1,1,-1,1,0),(false,-1,1,-1,1,0),(false,0,1,-1,0,0),(true,0,1,-1,0,0),(true,0,2,-1,0,-1),(false,0,2,-1,0,-1),(false,1,2,-1,-1,-1),(true,1,2,-1,-1,-1),(true,1,1,-2,-1,1),(true,1,0,-3,-1,4),(false,1,0,-3,-1,4),(false,0,0,-3,2,4),(true,0,0,-3,2,4),(true,0,1,-3,2,1),(false,0,1,-3,2,1),(false,-1,1,-3,5,1),(true,-1,1,-3,5,1),(true,-1,0,-2,4,3),(false,-1,0,-2,4,3),(false,0,0,-2,2,3),(false,1,0,-2,0,3),(true,1,0,-2,0,3),(true,1,1,-1,0,1),(true,1,2,0,0,0),(false,1,2,0,0,0),(false,0,2,0,0,0),(true,0,2,0,0,0),(true,0,1,0,0,0),(true,0,0,0,0,0),(false,0,0,0,0,0),(false,-1,0,0,0,0),(true,-1,0,0,0,0),(true,-1,1,-1,1,0),(false,-1,1,-1,1,0),(false,0,1,-1,0,0),(true,0,1,-1,0,0),(true,0,0,-1,0,1),(false,0,0,-1,0,1),(false,1,0,-1,-1,1),(true,1,0,-1,-1,1),(true,1,1,0,-1,0),(true,1,2,1,-1,0),(false,1,2,1,-1,0),(false,0,2,1,-2,0),(true,0,2,1,-2,0),(true,0,1,1,-2,-1),(false,0,1,1,-2,-1),(false,-1,1,1,-3,-1),(true,-1,1,1,-3,-1),(true,-1,0,2,-4,-3),(false,-1,0,2,-4,-3),(false,0,0,2,-2,-3),(true,0,0,2,-2,-3),(true,0,1,2,-2,-1),(true,0,2,2,-2,1),(false,0,2,2,-2,1),(false,1,2,2,0,1),(true,1,2,2,0,1),(true,1,1,1,0,0),(true,1,0,0,0,0),(false,1,0,0,0,0),(false,0,0,0,0,0),(false,-1,0,0,0,0),(true,-1,0,0,0,0),(true,-1,1,-1,1,0),(false,-1,1,-1,1,0),(false,0,1,-1,0,0),(true,0,1,-1,0,0),(true,0,0,-1,0,1),(false,0,0,-1,0,1),(false,1,0,-1,-1,1),(true,1,0,-1,-1,1),(true,1,1,0,-1,0),(true,1,2,1,-1,0),(false,1,2,1,-1,0),(false,0,2,1,-2,0),(true,0,2,1,-2,0),(true,0,1,1,-2,-1),(false,0,1,1,-2,-1),(false,-1,1,1,-3,-1),(true,-1,1,1,-3,-1),(true,-1,0,2,-4,-3),(false,-1,0,2,-4,-3),(false,0,0,2,-2,-3),(false,1,0,2,0,-3),(true,1,0,2,0,-3),(true,1,1,3,0,-1),(true,1,2,4,0,2),(false,1,2,4,0,2),(false,0,2,4,-4,2),(true,0,2,4,-4,2),(true,0,1,4,-4,-2),(true,0,0,4,-4,-6),(false,0,0,4,-4,-6),(false,-1,0,4,-8,-6),(true,-1,0,4,-8,-6),(true,-1,1,3,-7,-2),(false,-1,1,3,-7,-2),(false,0,1,3,-4,-2),(true,0,1,3,-4,-2),(true,0,2,3,-4,1),(false,0,2,3,-4,1),(false,1,2,3,-1,1),(true,1,2,3,-1,1),(true,1,1,2,-1,-1),(true,1,0,1,-1,-2),(false,1,0,1,-1,-2),(false,0,0,1,-2,-2),(true,0,0,1,-2,-2),(true,0,1,1,-2,-1),(false,0,1,1,-2,-1),(false,-1,1,1,-3,-1),(true,-1,1,1,-3,-1),(true,-1,0,2,-4,-3),(false,-1,0,2,-4,-3),(false,0,0,2,-2,-3),(true,0,0,2,-2,-3),(true,0,1,2,-2,-1),(true,0,2,2,-2,1),(false,0,2,2,-2,1),(false,1,2,2,0,1),(true,1,2,2,0,1),(true,1,1,1,0,0),(true,1,0,0,0,0),(false,1,0,0,0,0),(false,0,0,0,0,0)]
def w2 : Array P := #[1,2,1,2,0,2,0,2,0,2,1,1,2,1,2,0,2,1,2,0,2,0,2,1,1,2,0,2,0,0,2,1,1,2,1,2,0,2,1,2,0,2,0,0,2,1,2,1,2,1,2,0,2,0,0,2,1,1,2,1,2,0,0,2,1,2,1,2,0,2,1,2,0,2,0,0,2,1,2,1,2,1,2,0,2,0,2,1,1,2,0,2,0,0,2,1,1,2,1,2,0,2,0,2,0,2,1,1,2,1,2,0,2,1,2,0,2,0,0,2,1,1,2,1,2,0,0,2]
def t2 : Array State := #[(false,0,0,0,0,0),(false,-1,0,0,0,0),(true,-1,0,0,0,0),(true,-1,-1,1,-1,-1),(false,-1,-1,1,-1,-1),(false,0,-1,1,0,-1),(true,0,-1,1,0,-1),(true,0,0,1,0,0),(false,0,0,1,0,0),(false,1,0,1,1,0),(true,1,0,1,1,0),(true,1,-1,0,1,0),(true,1,-2,-1,1,1),(false,1,-2,-1,1,1),(false,0,-2,-1,2,1),(true,0,-2,-1,2,1),(true,0,-1,-1,2,0),(false,0,-1,-1,2,0),(false,-1,-1,-1,3,0),(true,-1,-1,-1,3,0),(true,-1,0,-2,4,-1),(false,-1,0,-2,4,-1),(false,0,0,-2,2,-1),(true,0,0,-2,2,-1),(true,0,-1,-2,2,1),(true,0,-2,-2,2,3),(false,0,-2,-2,2,3),(false,1,-2,-2,0,3),(true,1,-2,-2,0,3),(true,1,-1,-1,0,1),(true,1,0,0,0,0),(false,1,0,0,0,0),(false,0,0,0,0,0),(false,-1,0,0,0,0),(true,-1,0,0,0,0),(true,-1,-1,1,-1,-1),(false,-1,-1,1,-1,-1),(false,0,-1,1,0,-1),(true,0,-1,1,0,-1),(true,0,-2,1,0,-2),(false,0,-2,1,0,-2),(false,1,-2,1,1,-2),(true,1,-2,1,1,-2),(true,1,-1,2,1,-1),(true,1,0,3,1,1),(false,1,0,3,1,1),(false,0,0,3,-2,1),(true,0,0,3,-2,1),(true,0,-1,3,-2,-2),(false,0,-1,3,-2,-2),(false,-1,-1,3,-5,-2),(true,-1,-1,3,-5,-2),(true,-1,0,2,-4,1),(false,-1,0,2,-4,1),(false,0,0,2,-2,1),(false,1,0,2,0,1),(true,1,0,2,0,1),(true,1,-1,1,0,0),(true,1,-2,0,0,0),(false,1,-2,0,0,0),(false,0,-2,0,0,0),(true,0,-2,0,0,0),(true,0,-1,0,0,0),(true,0,0,0,0,0),(false,0,0,0,0,0),(false,-1,0,0,0,0),(true,-1,0,0,0,0),(true,-1,-1,1,-1,-1),(false,-1,-1,1,-1,-1),(false,0,-1,1,0,-1),(true,0,-1,1,0,-1),(true,0,-2,1,0,-2),(false,0,-2,1,0,-2),(false,1,-2,1,1,-2),(true,1,-2,1,1,-2),(true,1,-1,2,1,-1),(true,1,0,3,1,1),(false,1,0,3,1,1),(false,0,0,3,-2,1),(true,0,0,3,-2,1),(true,0,-1,3,-2,-2),(false,0,-1,3,-2,-2),(false,-1,-1,3,-5,-2),(true,-1,-1,3,-5,-2),(true,-1,0,2,-4,1),(false,-1,0,2,-4,1),(false,0,0,2,-2,1),(true,0,0,2,-2,1),(true,0,-1,2,-2,-1),(true,0,-2,2,-2,-3),(false,0,-2,2,-2,-3),(false,1,-2,2,0,-3),(true,1,-2,2,0,-3),(true,1,-1,3,0,-1),(true,1,0,4,0,2),(false,1,0,4,0,2),(false,0,0,4,-4,2),(false,-1,0,4,-8,2),(true,-1,0,4,-8,2),(true,-1,-1,5,-9,-3),(false,-1,-1,5,-9,-3),(false,0,-1,5,-4,-3),(true,0,-1,5,-4,-3),(true,0,0,5,-4,2),(false,0,0,5,-4,2),(false,1,0,5,1,2),(true,1,0,5,1,2),(true,1,-1,4,1,-2),(true,1,-2,3,1,-5),(false,1,-2,3,1,-5),(false,0,-2,3,-2,-5),(true,0,-2,3,-2,-5),(true,0,-1,3,-2,-2),(false,0,-1,3,-2,-2),(false,-1,-1,3,-5,-2),(true,-1,-1,3,-5,-2),(true,-1,0,2,-4,1),(false,-1,0,2,-4,1),(false,0,0,2,-2,1),(false,1,0,2,0,1),(true,1,0,2,0,1),(true,1,-1,1,0,0),(true,1,-2,0,0,0),(false,1,-2,0,0,0),(false,0,-2,0,0,0),(true,0,-2,0,0,0),(true,0,-1,0,0,0),(true,0,0,0,0,0),(false,0,0,0,0,0)]

def word (k : Fin 3) : Array P := ![w0,w1,w2] k
def chart (k : Fin 3) : Array State := ![t0,t1,t2] k

def prime (p : Fin 2) : Nat := ![5,7] p
def coefficients (p : Fin 2) (k : Fin 3) : Nat × Nat :=
  (![(![(4,2),(1,3),(1,2)] : Fin 3 → Nat × Nat),
      (![(6,3),(1,4),(1,3)] : Fin 3 → Nat × Nat)] : Fin 2 → Fin 3 → Nat × Nat) p k

def rowC (k : Fin 3) (i : Nat) : Coord := (chart k)[i]!.2
def di (a b : Coord) : ℤ := b.1-a.1
def dj (a b : Coord) : ℤ := b.2.1-a.2.1
def dc (a b : Coord) : ℤ := b.2.2.1-a.2.2.1
def du (a b : Coord) : ℤ := b.2.2.2.1-a.2.2.2.1
def dv (a b : Coord) : ℤ := b.2.2.2.2-a.2.2.2.2

instance (i : ℤ) : Decidable (Range i) := by unfold Range; infer_instance

theorem size : ∀ k : Fin 3, (word k).size=128 := by decide +kernel
theorem zero : ∀ k : Fin 3, (chart k)[0]! = (false,0,0,0,0,0) := by decide +kernel
theorem steps : ∀ (k : Fin 3) (i : Fin 128),
    Push (chart k)[i.val]! (word k)[i.val]! = (chart k)[i.val+1]! := by decide +kernel
theorem ranged : ∀ (k : Fin 3) (i : Fin 128), Range (rowC k i.val).1 := by decide +kernel

def oriented (p : Nat) (u v : Nat) (c a b : ℤ) : Prop :=
  (c=(p:ℤ) ∧ a%(p:ℤ)=(u:ℤ) ∧ b%(p:ℤ)=(v:ℤ)) ∨
  (c=-(p:ℤ) ∧ (-a)%(p:ℤ)=(u:ℤ) ∧ (-b)%(p:ℤ)=(v:ℤ))
instance (p u v : Nat) (c a b : ℤ) : Decidable (oriented p u v c a b) := by
  unfold oriented
  infer_instance

def certified (p : Fin 2) (k : Fin 3) (i j : Fin 128) : Prop :=
  let a := rowC k i.val
  let b := rowC k j.val
  i.val<j.val → (chart k)[i.val]!.1=(chart k)[j.val]!.1 →
  di a b=0 → dj a b=0 → (dc a b).natAbs=prime p →
  oriented (prime p) (coefficients p k).1 (coefficients p k).2 (dc a b) (du a b) (dv a b)
instance (p : Fin 2) (k : Fin 3) (i j : Fin 128) : Decidable (certified p k i j) := by
  unfold certified
  infer_instance

private theorem one0 : ∀ i j : Fin 128, certified 0 0 i j := by decide +kernel
private theorem one1 : ∀ i j : Fin 128, certified 0 1 i j := by decide +kernel
private theorem one2 : ∀ i j : Fin 128, certified 0 2 i j := by decide +kernel
private theorem two0 : ∀ i j : Fin 128, certified 1 0 i j := by decide +kernel
private theorem two1 : ∀ i j : Fin 128, certified 1 1 i j := by decide +kernel
private theorem two2 : ∀ i j : Fin 128, certified 1 2 i j := by decide +kernel

theorem cert (p : Fin 2) (k : Fin 3) (i j : Fin 128) : certified p k i j := by
  fin_cases p <;> fin_cases k
  · exact one0 i j
  · exact one1 i j
  · exact one2 i j
  · exact two0 i j
  · exact two1 i j
  · exact two2 i j

theorem classify (x y : G) (nil : LS G 3=⊥) (k : Fin 3) (i : Nat) (hi : i≤128) :
    pathAt x y (word k) i=Vert x y (chart k)[i]! := by
  apply chartSound x y nil (word k) (chart k) (zero k) ?_ ?_ i (by rw [size]; exact hi)
  · intro j hj
    rw [size] at hj
    exact steps k ⟨j,hj⟩
  · intro j hj
    rw [size] at hj
    exact ranged k ⟨j,hj⟩

theorem collision_relation (p : Fin 2) (k : Fin 3) (x y : G) (nil : LS G 3=⊥)
    (u_tor : (portU x y)^(prime p)=1) (v_tor : (portV x y)^(prime p)=1)
    (i j : Fin 128) (ij : i.val<j.val)
    (gap_i : di (rowC k i.val) (rowC k j.val)=0)
    (gap_j : dj (rowC k i.val) (rowC k j.val)=0)
    (gap_c : (dc (rowC k i.val) (rowC k j.val)).natAbs=prime p)
    (eq : pathAt x y (word k) i.val=pathAt x y (word k) j.val) :
    (portC x y)^(prime p)*(portU x y)^((coefficients p k).1)*
      (portV x y)^((coefficients p k).2)=1 := by
  rw [classify x y nil k i.val i.isLt.le,classify x y nil k j.val j.isLt.le] at eq
  have side := congrArg Prod.fst eq
  have M := congrArg Prod.snd eq
  let a := rowC k i.val
  let b := rowC k j.val
  have i_eq : a.1=b.1 := (sub_eq_zero.mp gap_i).symm
  have j_eq : a.2.1=b.2.1 := (sub_eq_zero.mp gap_j).symm
  have E := diff_one x y nil a b i_eq j_eq M
  have F := cert p k i j ij side gap_i gap_j gap_c
  let c := portC x y
  let u := portU x y
  let v := portV x y
  have project (d e : ℤ) (hd : d%((prime p):ℤ)=((coefficients p k).1:ℤ))
      (he : e%((prime p):ℤ)=((coefficients p k).2:ℤ))
      (W : mon c u v (prime p) d e=1) :
      c^(prime p)*u^((coefficients p k).1)*v^((coefficients p k).2)=1 := by
    unfold mon at W
    rw [reduce_pow u (prime p) u_tor d,reduce_pow v (prime p) v_tor e,hd,he,
        zpow_natCast,zpow_natCast,zpow_natCast] at W
    exact W
  change mon c u v (dc a b) (du a b) (dv a b)=1 at E
  rcases F with ⟨c0,d,e⟩ | ⟨c0,d,e⟩
  · rw [c0] at E
    exact project _ _ d e E
  · have H := reverse_one c u v (central_u x y nil c).symm (central_v x y nil c).symm
      (central_u x y nil v) E
    rw [c0,neg_neg] at H
    exact project _ _ d e H

end Ribbon8Small
#print axioms Ribbon8Small.cert
#print axioms Ribbon8Small.collision_relation
