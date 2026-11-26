import HaarC5Haar
import HaarK33AllPorts
import Mathlib.Tactic.Ring
import Mathlib.GroupTheory.SpecificGroups.Cyclic

namespace HaarC5AllPorts
open HaarAllNoncommuting
variable {G : Type*} [Group G]
abbrev Q := Multiplicative (ZMod 5)

def rescale (s : ZMod 5) : Q →* Q where
  toFun z := Multiplicative.ofAdd (s*z.toAdd)
  map_one' := by simp
  map_mul' a b := by simp [mul_add]

theorem twice_ports [Finite G] (odd : Odd (Nat.card G))
    (π : G →* Q) (x y : G) (nx : (π x).toAdd ≠ 0)
    (twice : (π y).toAdd = 2*(π x).toAdd)
    (hc : ∀ a b : π.ker, a*b=b*a) :
    ∃ n, n ∈ [4,8,16,32] ∧ HasCycle x y n := by
  let r := (π x).toAdd
  have inv : ∀ (a : ZMod 5), a≠0 → ∃ b : ZMod 5, b*a=1 := by decide +kernel
  obtain ⟨b,bR⟩ := inv r nx
  let f := (rescale b).comp π
  have hx : (f x).toAdd=1 := bR
  have hy : (f y).toAdd=2 := by
    change b*(π y).toAdd=2
    rw [twice]
    change b*(2*r)=2
    calc
      _ = 2*(b*r) := by ring
      _ = 2 := by rw [bR,mul_one]
  letI : Fact (∀ a b : f.ker, a*b=b*a) := ⟨by
    intro a k
    apply Subtype.ext
    have h (a : f.ker) : π (a:G)=1 := by
      have E : (f (a:G)).toAdd=0 := congrArg Multiplicative.toAdd a.property
      change b*(π (a:G)).toAdd=0 at E
      have rb : r*b=1 := (mul_comm r b).trans bR
      have Z := congrArg (fun q : ZMod 5 => r*q) E
      have Z' : (π (a:G)).toAdd=0 := by simpa [←mul_assoc,rb] using Z
      exact Multiplicative.toAdd.injective Z' 
    exact congrArg (fun z : π.ker => (z : G)) (hc ⟨a,h a⟩ ⟨k,h k⟩)⟩
  have cardK : Odd (Nat.card f.ker) := Odd.of_dvd_nat odd (Subgroup.card_subgroup_dvd_card f.ker)
  exact HaarC5Haar.kernel_odd f x y hx hy cardK

theorem any_ports [Finite G] (odd : Odd (Nat.card G))
    (π : G →* Q) (x y : G) (nx : x≠1) (ny : y≠1) (nd : x≠y)
    (hc : ∀ a b : π.ker, a*b=b*a) :
    ∃ n, n ∈ [4,8,16,32] ∧ HasCycle x y n := by
  by_cases hx : π x = 1
  · by_cases hy : π y = 1
    · have c : Commute x y := congrArg Subtype.val (hc ⟨x,hx⟩ ⟨y,hy⟩)
      rcases HaarAbel.commute_case x y c nx ny nd with C|C|C
      · exact ⟨4,by decide,C⟩
      · exact ⟨8,by decide,C⟩
      · exact ⟨16,by decide,C⟩
    · exact HaarK33Collapse.kernel_one_port π odd x y nx hx hy hc
  by_cases hy : π y=1
  · obtain ⟨n,hn,C⟩ := HaarK33Collapse.kernel_one_port π odd y x ny hy hx hc
    exact ⟨n,hn,HaarK33Haar.swap_cycle x y C⟩
  by_cases same : π x=π y
  · have h0 : π (y*x⁻¹)=1 := by simp [← same]
    have hn0 : y*x⁻¹ ≠ 1 := by
      intro e
      exact nd (by simpa using (mul_inv_eq_one.mp e).symm)
    have h1 : π x⁻¹≠1 := by simpa using hx
    obtain ⟨n,hn,C⟩ := HaarK33Collapse.kernel_one_port π odd _ _ hn0 h0 h1 hc
    exact ⟨n,hn,HaarK33AllPorts.undo_normalize x y C⟩
  have arithmetic : ∀ a b : ZMod 5, a≠0 → b≠0 → a≠b →
      b=2*a ∨ a=2*b ∨ b= -a := by decide +kernel
  have x0 : (π x).toAdd≠0 := fun h => hx (Multiplicative.toAdd.injective h)
  have y0 : (π y).toAdd≠0 := fun h => hy (Multiplicative.toAdd.injective h)
  have d0 : (π x).toAdd≠(π y).toAdd := fun h => same (Multiplicative.toAdd.injective h)
  rcases arithmetic _ _ x0 y0 d0 with d|d|d
  · exact twice_ports odd π x y x0 d hc
  · obtain ⟨n,hn,C⟩ := twice_ports odd π y x y0 d hc
    exact ⟨n,hn,HaarK33Haar.swap_cycle x y C⟩
  · have in0 : (π x⁻¹).toAdd≠0 := by simpa using x0
    have eq : (π (y*x⁻¹)).toAdd=2*(π x⁻¹).toAdd := by
      simp only [map_mul,map_inv,toAdd_mul,toAdd_inv,d]
      ring
    obtain ⟨n,hn,C⟩ := twice_ports odd π x⁻¹ (y*x⁻¹) in0 eq hc
    exact ⟨n,hn,HaarK33AllPorts.undo_normalize x y (HaarK33Haar.swap_cycle _ _ C)⟩

theorem normal_abelian_index_five [Finite G] (odd : Odd (Nat.card G))
    (A : Subgroup G) [A.Normal] (index : Nat.card (G ⧸ A) = 5)
    (hc : ∀ a b : A, a*b=b*a) (x y : G) (nx : x≠1) (ny : y≠1) (nd : x≠y) :
    ∃ n, n ∈ [4,8,16,32] ∧ HasCycle x y n := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have c5 : Nat.card Q = 5 := by
    change Nat.card (ZMod 5)=5
    rw [Nat.card_eq_fintype_card,ZMod.card]
  let e : (G ⧸ A) ≃* Q := mulEquivOfPrimeCardEq index c5
  let f := e.toMonoidHom.comp (QuotientGroup.mk' A)
  apply any_ports odd f x y nx ny nd
  intro a b
  apply Subtype.ext
  have original (a : f.ker) : (a : G) ∈ A := by
    apply (QuotientGroup.eq_one_iff (N:=A) _).mp
    apply e.injective
    change f a = e 1
    rw [map_one]
    exact a.property
  exact congrArg (fun z : A => (z : G)) (hc ⟨a,original a⟩ ⟨b,original b⟩)

end HaarC5AllPorts
#print axioms HaarC5AllPorts.normal_abelian_index_five
