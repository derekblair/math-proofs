import HaarK33Collapse
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace HaarK33AllPorts
open HaarAllNoncommuting
variable {G : Type*} [Group G]

theorem undo_normalize (x y : G) {n : ℕ}
    (C : HasCycle (y*x⁻¹) x⁻¹ n) : HasCycle x y n := by
  obtain ⟨v,inj,edges⟩ := C
  let f (a : Bool × G) : Bool × G := (a.1, if a.1 then a.2*x else a.2)
  have fi : Function.Injective f := by
    rintro ⟨s,a⟩ ⟨t,b⟩ h
    have st : s=t := congrArg Prod.fst h
    subst t
    have ab : a=b := by
      have H := congrArg Prod.snd h
      cases s
      · exact H
      · exact mul_right_cancel H
    rw [ab]
  refine ⟨f ∘ v, fi.comp inj, fun i => ?_⟩
  let j : Fin n := ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
  have e := edges i
  change HaarCycle.haarAdj (y*x⁻¹) x⁻¹ (v i) (v j) at e
  change HaarCycle.haarAdj x y (f (v i)) (f (v j))
  cases s : (v i).1
  · simp only [HaarCycle.haarAdj,s,Bool.false_eq_true,ite_false] at e
    have t : (v j).1=true := e.1
    simp only [HaarCycle.haarAdj,f,s,t,Bool.false_eq_true,ite_false,ite_true,true_and]
    rcases e.2 with eq|eq|eq
    · exact Or.inr (Or.inl (by rw [eq]))
    · exact Or.inr (Or.inr (by rw [eq]; group))
    · exact Or.inl (by rw [eq]; group)
  · simp only [HaarCycle.haarAdj,s,ite_true] at e
    have t : (v j).1=false := e.1
    simp only [HaarCycle.haarAdj,f,s,t,Bool.false_eq_true,ite_true,ite_false,true_and]
    rcases e.2 with eq|eq|eq
    · exact Or.inr (Or.inl (by rw [eq]))
    · exact Or.inr (Or.inr (by rw [eq]; group))
    · exact Or.inl (by rw [eq]; group)

theorem any_ports [Finite G] (odd : Odd (Nat.card G))
    (π : G →* Multiplicative (ZMod 3)) (x y : G) (nx : x≠1) (ny : y≠1) (nd : x≠y)
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
    exact ⟨n,hn,undo_normalize x y C⟩
  · letI : Fact (∀ a b : π.ker, a*b=b*a) := ⟨hc⟩
    exact HaarK33Haar.odd_group_distinct_ports π x y odd (fun h => hx (Multiplicative.toAdd.injective h))
      (fun h => hy (Multiplicative.toAdd.injective h)) (fun h => same (Multiplicative.toAdd.injective h))

theorem normal_abelian_index_three [Finite G] (odd : Odd (Nat.card G))
    (A : Subgroup G) [A.Normal] (index : Nat.card (G ⧸ A) = 3)
    (hc : ∀ a b : A, a*b=b*a) (x y : G) (nx : x≠1) (ny : y≠1) (nd : x≠y) :
    ∃ n, n ∈ [4,8,16,32] ∧ HasCycle x y n := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have c3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    change Nat.card (ZMod 3)=3
    rw [Nat.card_eq_fintype_card,ZMod.card]
  let e : (G ⧸ A) ≃* Multiplicative (ZMod 3) := mulEquivOfPrimeCardEq index c3
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

end HaarK33AllPorts
#print axioms HaarK33AllPorts.any_ports
#print axioms HaarK33AllPorts.normal_abelian_index_three
