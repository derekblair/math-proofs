import HostWagnerColor
import CoreDensityColor
import Mathlib.Logic.Equiv.Set

namespace Erdős151.H12
open Wagner

variable {V : Type*} [Fintype V] [DecidableEq V]

def edgeRost (G : SimpleGraph V) [DecidableRel G.Adj] : Edges G ↪ Finset V :=
  ⟨Subtype.val,Subtype.val_injective⟩

def triRost (G : SimpleGraph V) [DecidableRel G.Adj] : Triangles G ↪ Finset V :=
  ⟨Subtype.val,Subtype.val_injective⟩

theorem host_iff_of_ne (G : SimpleGraph V) [DecidableRel G.Adj] {a b : V} (ne : a≠b) :
    hostRel (edgeRost G) a b ↔ G.Adj a b := by
  constructor
  · rintro ⟨e,ea,eb⟩
    have h := SimpleGraph.mem_cliqueFinset_iff.mp e.property
    exact h.isClique ea eb ne
  · intro h
    refine ⟨pairEdge G h,?_,?_⟩ <;> change _ ∈ ({a,b}:Finset V) <;> simp

theorem actual_locally_wagner_safe (G : SimpleGraph V) [DecidableRel G.Adj]
    (origin : V)
    (conn : ∀ a b : V, Relation.ReflTransGen G.Adj a b)
    (iso : ∀ v : V, ∃ e : Fin 8 ≃ {x : V // x≠v ∧ G.Adj v x},
      ∀ i j, WagnerFin8.Adj i j ↔ G.Adj (e i).val (e j).val) :
    ∃ c : V→V→Bool, (∀ a b,c a b=c b a) ∧ BikovLocal.Safe G.Adj c := by
  classical
  let E := edgeRost G
  let T := triRost G
  let s (v : V) := Classical.choose (iso v)
  have holds v := Classical.choose_spec (iso v)
  let lift (v : V) : {x : V // x≠v ∧ G.Adj v x} ≃ {x : V // x≠v ∧ hostRel E v x} :=
    Equiv.subtypeEquivRight (fun x => by
      constructor
      · intro h; exact ⟨h.1,(host_iff_of_ne G h.1.symm).mpr h.2⟩
      · intro h; exact ⟨h.1,(host_iff_of_ne G h.1.symm).mp h.2⟩)
  let slot (v : V) := (s v).trans (lift v)
  have Hs (v : V) (i : Fin 8) : (slot v i).val = (s v i).val := rfl
  have fwd (v : V) (i j : Fin 8) (h : WagnerFin8.Adj i j) :
      hostRel E (slot v i).val (slot v j).val := by
    have h' := (holds v i j).mp h
    rw [Hs,Hs]
    exact (host_iff_of_ne G h'.ne).mpr h'
  have htri (v : V) (i j : Fin 8) (h:WagnerFin8.Adj i j) :
      ∃ t : Triangles G, T t={v,(slot v i).val,(slot v j).val} := by
    let a := (s v i).val
    let b := (s v j).val
    have ha : G.Adj v a := (s v i).property.2
    have hb : G.Adj v b := (s v j).property.2
    have hab := (holds v i j).mp h
    exact ⟨triangleNode G ha hab hb,rfl⟩
  let w : HostWagnerLinks E T := ⟨slot,fwd,htri⟩
  have rev : w.Reflects := by
    intro v i j ne hij
    have d : (s v i).val ≠ (s v j).val := fun h => ne ((s v).injective (Subtype.ext h))
    exact (holds v i j).mpr ((host_iff_of_ne G d).mp hij)
  have cl : HostWagnerLinks.TrianglesClosed E T := by
    intro t a b ne ha hb
    exact (host_iff_of_ne G ne).mpr
      ((SimpleGraph.mem_cliqueFinset_iff.mp t.property).isClique ha hb ne)
  have ec (e : Edges G) : (E e).card=2 :=
    (SimpleGraph.mem_cliqueFinset_iff.mp e.property).card_eq
  have tc (t : Triangles G) : (T t).card=3 :=
    (SimpleGraph.mem_cliqueFinset_iff.mp t.property).card_eq
  have hconn (a b : V) : Relation.ReflTransGen (hostRel E) a b := by
    induction conn a b with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ h ih => exact ih.tail ((host_iff_of_ne G h.ne).mpr h)
  obtain ⟨c,good⟩ := w.edge_triangle_bichromatic rev ec tc cl hconn origin
  exact to_safe_of_mixed G c good

#print axioms actual_locally_wagner_safe
end Erdős151.H12
