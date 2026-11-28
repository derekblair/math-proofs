import ActualLinkTransit

namespace Erdős151.H13
open Erdős151.H12 Erdős151.H12.Wagner

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def incidentTriangles (G : SimpleGraph V) [DecidableRel G.Adj] :
    Triangles G → Finset (Edges G) := hostIncEdge (edgeRost G) (triRost G)

private theorem adjacent_spokes (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (a b : Lk G v) (h : G.Adj a.val b.val) :
    coTriangle (incidentTriangles G) (actualSpoke G v a) (actualSpoke G v b) := by
  let t := triangleNode G a.property h b.property
  refine ⟨t,(hostInc_mem _ _ _ _).mpr ?_,(hostInc_mem _ _ _ _).mpr ?_⟩
  · rw [spoke_set]
    change ({v,a.val} : Finset V) ⊆ {v,a.val,b.val}
    simp [Finset.insert_subset_iff]
  · rw [spoke_set]
    change ({v,b.val} : Finset V) ⊆ {v,a.val,b.val}
    simp [Finset.insert_subset_iff]

private theorem steps_of_reflTransGen {A : Type*} [Fintype A] [DecidableEq A] {R : A → A → Prop} {a b : A}
    (p : Relation.ReflTransGen R a b) : ∃ n, Steps R n a b := by
  induction p with
  | refl => exact ⟨0,Steps.zero _⟩
  | tail _ h ih => obtain ⟨_,s⟩ := ih; exact Steps.concat s (Steps.more h (Steps.zero _))

theorem link_coTriangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (conn : LinkDeletionConnected G) (v : V) (e f : Edges G)
    (he : v ∈ edgeRost G e) (hf : v ∈ edgeRost G f) :
    ∃ n, Steps (coTriangle (incidentTriangles G)) n e f := by
  obtain ⟨a,ea⟩ := spoke_of_mem G v e he
  obtain ⟨b,eb⟩ := spoke_of_mem G v f hf
  have pp := conn v ∅ (by simp) a b (by simp) (by simp)
  have push {a b : Lk G v}
      (p : Relation.ReflTransGen (fun x y : Lk G v => G.Adj x.val y.val ∧
        x ∉ (∅ : Finset (Lk G v)) ∧ y ∉ (∅ : Finset (Lk G v))) a b) :
      Relation.ReflTransGen (coTriangle (incidentTriangles G))
        (actualSpoke G v a) (actualSpoke G v b) := by
    induction p with
    | refl => exact .refl
    | tail _ h ih => exact ih.tail (adjacent_spokes G v _ _ h.1)
  exact steps_of_reflTransGen (ea ▸ eb ▸ push pp)

theorem actual_coTriangle_connected (G : SimpleGraph V) [DecidableRel G.Adj]
    (conn : ∀ a b : V, Relation.ReflTransGen G.Adj a b)
    (links : LinkDeletionConnected G)
    (p : Edges G) (origin : V) (hp : origin∈edgeRost G p) :
    ∀ e, ∃ n, Steps (coTriangle (incidentTriangles G)) n e p := by
  let P (a : V) := ∀ e : Edges G, a ∈ edgeRost G e →
    ∃ n, Steps (coTriangle (incidentTriangles G)) n e p
  have localStep {a b : V} (ab : G.Adj a b) : P b → P a := by
    intro pb e ea
    let f := pairEdge G ab
    have fa : a ∈ edgeRost G f := by change a ∈ ({a,b} : Finset V); simp
    have fb : b ∈ edgeRost G f := by change b ∈ ({a,b} : Finset V); simp
    obtain ⟨_,ef⟩ := link_coTriangle G links a e f ea fa
    obtain ⟨_,fp⟩ := pb f fb
    exact Steps.concat ef fp
  have walk {a b : V} (h : Relation.ReflTransGen G.Adj a b) : P b → P a := by
    induction h with
    | refl => exact id
    | tail _ step ih => intro hb; exact ih (localStep step hb)
  intro e
  have card : (edgeRost G e).card=2 := (SimpleGraph.mem_cliqueFinset_iff.mp e.property).card_eq
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0 < (edgeRost G e).card by omega)
  exact walk (conn v origin) (fun f hf => link_coTriangle G links origin f p hf hp) e hv

#print axioms actual_coTriangle_connected
end Erdős151.H13
