import PetersenSharpGraph

namespace PetersenSharp

def baseEdge (u v : B) : Prop := ∃ p : P, base u p = v

theorem base_next_inj (u : B) : Function.Injective (base u) := by decide +revert

theorem projected {u v : V} (e : edge u v) : baseEdge u.1 v.1 := by
  obtain ⟨p,h⟩ := e
  exact ⟨p,congrArg Prod.fst h⟩

/-- Local bijection from the lifted graph to the Petersen base. -/
theorem unique_neighbor_lift (u : V) (v : B) (h : baseEdge u.1 v) :
    ∃! w : V, edge u w ∧ w.1=v := by
  obtain ⟨p,rfl⟩ := h
  refine ⟨next u p,⟨⟨p,rfl⟩,rfl⟩,?_⟩
  intro w ew
  obtain ⟨⟨q,rfl⟩,eq⟩ := ew
  have qp : q = p := base_next_inj u.1 eq
  rw [qp]

theorem shift_edge (d : D) (u v : V) :
    edge (shift d u) (shift d v) ↔ edge u v := by
  constructor
  · rintro ⟨p,e⟩
    exact ⟨p,shift_inj d ((shift_next d u p).trans e)⟩
  · rintro ⟨p,rfl⟩
    exact ⟨p,(shift_next d u p).symm⟩

/-- Deck translations act freely and transitively on each projection fiber. -/
theorem deck (u v : V) (h : u.1=v.1) : ∃! d : D, shift d u = v := by
  rcases u with ⟨a,z⟩
  rcases v with ⟨b,t⟩
  refine ⟨t-z,?_ ,?_⟩
  · refine Prod.ext ?_ ?_
    · exact h
    · change z+(t-z)=t
      abel
  · intro d e
    have ez : z+d=t := congrArg (Prod.snd : V → D) e
    apply (add_left_cancel (a:=z))
    rw [ez]
    abel

theorem order : Fintype.card V = 50 := by decide

end PetersenSharp

#print axioms PetersenSharp.unique_neighbor_lift
#print axioms PetersenSharp.deck
