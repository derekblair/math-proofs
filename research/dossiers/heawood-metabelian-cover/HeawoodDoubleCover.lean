import HeawoodDoubleGroup
import HeawoodDoubleGirth
import Mathlib.SetTheory.Cardinal.Finite

namespace HeawoodDoubleDeck
open HeawoodDouble HomologyThree
open HaarOrbitC7Voltage (B)

def base (u : V2) : B := u.1.1

def endVertex (u : V2) (b : B) : V2 :=
  let v : V1 := (b,u.1.2+bump u.1.1 b)
  (v,u.2+bump u.1 v)

theorem onto : Function.Surjective base := by
  intro b
  exact ⟨((b,0),0),rfl⟩

theorem edge_to_base {u v : V2} (e : Edge2 u v) :
    HeawoodGirthSix.Edge (base u) (base v) := e.1.1

theorem unique_lift (u : V2) (b : B) (e : HeawoodGirthSix.Edge (base u) b) :
    ∃! v : V2, Edge2 u v ∧ base v=b := by
  refine ⟨endVertex u b,⟨⟨⟨e,rfl⟩,rfl⟩,rfl⟩,?_⟩
  rintro v ⟨adj,proj⟩
  have V : v.1 = (endVertex u b).1 := by
    refine Prod.ext proj ?_
    change v.1.2=u.1.2+bump u.1.1 b
    exact adj.1.2.symm.trans (by rw [show v.1.1=b from proj])
  refine Prod.ext V ?_
  change v.2=u.2+bump u.1 ((endVertex u b).1)
  exact adj.2.symm.trans (by rw [V])

@[simp] theorem action_projects (d : Deck) (u : V2) : base (action d u)=base u := rfl

theorem finite_odd : Odd (Nat.card Deck) := by
  rw [Nat.card_congr coords,Nat.card_prod]
  have cord : Nat.card (ZMod 3)=3 := by rw [Nat.card_eq_fintype_card,ZMod.card]
  have oddfun (T : Type) [Finite T] : Odd (Nat.card (Lamp T)) := by
    change Odd (Nat.card ((T×T)→ZMod 3))
    rw [Nat.card_fun,cord]
    exact (by decide : Odd (3:ℕ)).pow
  exact (oddfun B).mul (oddfun V1)

end HeawoodDoubleDeck
#print axioms HeawoodDoubleDeck.unique_lift
#print axioms HeawoodDoubleDeck.finite_odd
