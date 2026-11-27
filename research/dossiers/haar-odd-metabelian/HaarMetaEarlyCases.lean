import HaarMetaAlgebraCore
import HaarK33AllPorts
import HaarC5AllPorts
import HaarStripHaar
import HaarAbel
import Mathlib.GroupTheory.SpecificGroups.Cyclic

namespace HaarMetaEarlyCases
open HaarAllNoncommuting HaarClass4Generate
variable {G Q : Type*} [Group G] [Group Q]
abbrev Good (x y : G) := ∃ n, n∈[4,8,16,32] ∧ HasCycle x y n

theorem collapse [Finite G] (odd : Odd (Nat.card G)) (f : G→*Q)
    (ab : ∀ a b : f.ker, a*b=b*a)
    (x y : G) (hx : x≠1) (hy : y≠1) (hne : x≠y) (xf : f x=1) : Good x y := by
  by_cases yf : f y=1
  · have c : Commute x y :=
      congrArg (fun a : f.ker => a.val) (ab ⟨x,xf⟩ ⟨y,yf⟩)
    rcases HaarAbel.commute_case x y c hx hy hne with h|h|h
    · exact ⟨4,by decide,h⟩
    · exact ⟨8,by decide,h⟩
    · exact ⟨16,by decide,h⟩
  · exact HaarK33Collapse.kernel_one_port f odd x y hx xf yf ab

theorem index_three [Finite G] (odd : Odd (Nat.card G)) (f : G→*Q)
    (onto : Function.Surjective f) (ab : ∀ a b : f.ker, a*b=b*a) (card : Nat.card Q=3)
    (x y : G) (hx : x≠1) (hy : y≠1) (hne : x≠y) : Good x y :=
  HaarK33AllPorts.normal_abelian_index_three odd f.ker
    ((Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f onto).toEquiv).trans card)
    ab x y hx hy hne

theorem index_five [Finite G] (odd : Odd (Nat.card G)) (f : G→*Q)
    (onto : Function.Surjective f) (ab : ∀ a b : f.ker, a*b=b*a) (card : Nat.card Q=5)
    (x y : G) (hx : x≠1) (hy : y≠1) (hne : x≠y) : Good x y :=
  HaarC5AllPorts.normal_abelian_index_five odd f.ker
    ((Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f onto).toEquiv).trans card)
    ab x y hx hy hne

theorem ap [Finite G] (odd : Odd (Nat.card G)) (f : G→*Q)
    (onto : Function.Surjective f) (ab : ∀ a b : f.ker, a*b=b*a)
    (x y : G) (hx : x≠1) (hy : y≠1) (hne : x≠y) (gen : Generates x y)
    (sq : f y=(f x)^(2:ℕ)) : Good x y := by
  letI : Fact (∀ a b : f.ker, a*b=b*a) := ⟨ab⟩
  letI : Finite Q := Finite.of_surjective f onto
  by_cases last : 6≤orderOf (f x)
  · exact HaarStripHaar.odd_ap f x y sq odd last
  have g : Subgroup.closure ({f x,f y}:Set Q)=⊤ := HaarClass4Generate.map_gen f onto gen
  have z : Subgroup.zpowers (f x)=⊤ := by
    refine top_unique ?_
    rw [←g]
    apply (Subgroup.closure_le _).mpr
    intro a e
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at e
    rcases e with rfl | rfl
    · exact Subgroup.mem_zpowers _
    · rw [sq]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  have card' : orderOf (f x)=Nat.card Q := orderOf_eq_card_of_zpowers_eq_top z
  have oddQ := HaarMetaAlgebraCore.odd_of_surj f onto odd
  have oo : orderOf (f x)=1 ∨ Nat.card Q=3 ∨ Nat.card Q=5 := by
    obtain ⟨a,e⟩ := oddQ
    omega
  rcases oo with h|h|h
  · exact collapse odd f ab x y hx hy hne (orderOf_eq_one_iff.mp h)
  · exact index_three odd f onto ab h x y hx hy hne
  · exact index_five odd f onto ab h x y hx hy hne

end HaarMetaEarlyCases
#print axioms HaarMetaEarlyCases.ap
