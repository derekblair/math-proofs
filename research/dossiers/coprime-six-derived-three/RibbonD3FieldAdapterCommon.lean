import RibbonD3FieldOutcome
import RibbonD3FieldUse
import RibbonD3Orbit

namespace RibbonD3Finite
open RibbonD3Stationary RibbonD3Orientation RibbonD3Field RibbonDerived3 RibbonP11
universe u v

theorem badLists : exactBad=(List.finRange 52).map (fun i => (getBad i).triple) := by
  decide +kernel

theorem fieldBadToBad {K : Type*} [Field K] (a b : Kˣ) (f : FieldBad a b) :
    ∃ p, PrimeBad p ∧ ∃ (e : ZMod p→+*K) (a' b' : ZMod p),
        e a'=(a:K) ∧ e b'=(b:K) ∧ Bad (p,a'.val,b'.val) := by
  obtain ⟨p,h,e,A,B,x,y,m⟩ := f
  rw [badLists] at m
  obtain ⟨i,_,eq⟩ := List.mem_map.mp m
  exact ⟨p,h,e,A,B,x,y,i,eq⟩

theorem embed_long {G : Type*} [Group G] {x y : G}
    (H : Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 ∨ Ribbon.Cycle x y 128) :
    LongGood x y := Or.inr (Or.inr (Or.inr H))

theorem swap_long {G : Type*} [Group G] {x y : G} (H : LongGood y x) : LongGood x y :=
  longUnact ⟨false,false,true⟩ x y H

end RibbonD3Finite
#print axioms RibbonD3Finite.fieldBadToBad
