import HaarP3Class4Dispatch
import HaarP3LayerGenConcrete

namespace HaarP3FifthData
open scoped commutatorElement
open HaarP3Class4Dispatch HaarP3LayerGen HaarClass4Ports HaarClass4Structure HaarClass4Normal
variable {G : Type*} [Group G]

structure Data (x y : G) where
  h0 : portV x y * portU x y * ⁅portU x y,x⁆ ∈ LS G 4
  h1 : portU x y ^ (3:ℕ) ∈ LS G 4
  h2 : ⁅portU x y,y⁆ * ⁅portU x y,x⁆ ∈ LS G 4
  ordA : orderOf (QuotientGroup.mk' (LS G 4) ⁅portU x y,x⁆)=3
  ordU : orderOf (QuotientGroup.mk' (LS G 3) (portU x y))=3
  ordC : 3∣orderOf (QuotientGroup.mk' (LS G 2) (portC x y))

theorem projectedU (x y : G) (E : Exceptional x y) :
    orderOf (QuotientGroup.mk' (LS G 3) (portU x y))=3 := by
  let f := QuotientGroup.mk' (LS G 4)
  let D := make (ls4quot_class4 G) (f x) (f y)
  have hA := E.1
  let a := ⁅portU x y,x⁆
  let u := portU x y
  have eqA : f a=D.a := by
    change f ⁅portU x y,x⁆=⁅portU (f x) (f y),f x⁆
    simp only [portU,portC,map_commutatorElement,map_inv]
  have eqU : f u=D.u := by
    change f (portU x y)=portU (f x) (f y)
    simp only [portU,portC,map_commutatorElement,map_inv]
  let ψ := QuotientGroup.mk' (LS G 3)
  have uc : (ψ u)^(3:ℕ)=1 := by
    have hu : u^(3:ℕ)∈LS G 4 := (QuotientGroup.eq_one_iff _).mp (by
      change f (u^(3:ℕ))=1
      rw [map_pow,eqU]
      exact E.2.2.1)
    rw [←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr
      (Subgroup.lowerCentralSeries_antitone _ (by decide : 3≤4) hu)
  have un : ψ u≠1 := by
    intro eq
    have ah : a∈LS G 4 := next_layer ((QuotientGroup.eq_one_iff _).mp eq) x
    have af : f a=1 := (QuotientGroup.eq_one_iff _).mpr ah
    change orderOf D.a=3 at hA
    rw [eqA] at af
    rw [af,orderOf_one] at hA
    omega
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact orderOf_eq_prime uc un

def data (x y : G) (E : Exceptional x y) : Data x y := by
  let f := QuotientGroup.mk' (LS G 4)
  let n4 := ls4quot_class4 G
  let D := make n4 (f x) (f y)
  let a := ⁅portU x y,x⁆
  let b := ⁅portU x y,y⁆
  let u := portU x y
  let v := portV x y
  have eA : f a=D.a := by
    change f ⁅portU x y,x⁆=⁅portU (f x) (f y),f x⁆
    simp only [portU,portC,map_commutatorElement,map_inv]
  have eB : f b=D.b := by
    change f ⁅portU x y,y⁆=⁅portU (f x) (f y),f y⁆
    simp only [portU,portC,map_commutatorElement,map_inv]
  have eU : f u=D.u := by
    change f (portU x y)=portU (f x) (f y)
    simp only [portU,portC,map_commutatorElement,map_inv]
  have eV : f v=D.v := by
    change f (portV x y)=portV (f x) (f y)
    simp only [portV,portC,map_commutatorElement,map_inv]
  have ou := projectedU x y E
  obtain ⟨oa,ev,cu,ca⟩ := E
  change orderOf D.a=3 at oa
  change D.v=D.u^2*D.a^2 at ev
  change D.u^3=1 at cu
  change D.a^3=1 at ca
  have hU : D.u^(3:ℕ) ∈ LS (G ⧸ LS G 4) 3 := by rw [cu]; exact Subgroup.one_mem _
  have hAt : D.a^(2:ℕ) ∈ LS (G ⧸ LS G 4) 3 :=
    Subgroup.pow_mem _ (tail_layers n4 (f x) (f y)).1 _
  have ⟨_,hb,_⟩ := pivotU n4 (f x) (f y) 2 hU _ hAt ev
  have oc := HaarP3Class4Order.c_order3 (portC x y) x (layer_c x y) ou
  refine ⟨?_,?_,?_,by rw [show QuotientGroup.mk' (LS G 4) a = f a by rfl,eA]; exact oa,ou,oc⟩
  · apply (QuotientGroup.eq_one_iff _).mp
    change f (v*u*a)=1
    rw [map_mul,map_mul,eV,eU,eA,ev,mul_assoc (D.u^2),
      ((D.ca D.u).pow_left 2).eq,←mul_assoc (D.u^2) D.u,←pow_succ,cu,one_mul,←pow_succ,ca]
  · apply (QuotientGroup.eq_one_iff _).mp
    change f (u^(3:ℕ))=1
    rw [map_pow,eU,cu]
  · apply (QuotientGroup.eq_one_iff _).mp
    change f (b*a)=1
    rw [map_mul,eB,eA,hb,←pow_succ,ca]

end HaarP3FifthData
#print axioms HaarP3FifthData.data
