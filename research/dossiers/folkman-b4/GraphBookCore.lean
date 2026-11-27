import FamilyCore
import FanoGraph
import Mathlib.Data.Finset.Powerset

namespace FolkmanB4
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite simple graph is given by its unordered two-element edge sets.
This lists precisely the edge sets of its ordinary triangles. -/
noncomputable def graphTriangles (G : Finset (Finset V)) : Finset (Finset (Finset V)) := by
  classical
  exact (G.powersetCard 3).filter fun B => ∃ a b c, Triangle a b c ∧ B={a,b,c}

theorem mem_graphTriangles {G : Finset (Finset V)} {T : Finset (Finset V)} :
    T ∈ graphTriangles G ↔ T⊆G ∧ T.card=3 ∧ ∃ a b c, Triangle a b c ∧ T={a,b,c} := by
  classical
  simp [graphTriangles,and_assoc]

def BookFree (G : Finset (Finset V)) : Prop :=
  ∀ e, ((graphTriangles G).filter fun t => e∈t).card≤3

omit [Fintype V] in
theorem triangle_rotate {a b c : Finset V} (h : Triangle a b c) :
    Triangle b c a := by
  obtain ⟨x,y,z,xy,xz,yz,rfl,rfl,rfl⟩ := h
  exact ⟨y,z,x,yz,Ne.symm xy,Ne.symm xz,rfl,rfl,rfl⟩

omit [Fintype V] in
theorem triangle_flip {a b c : Finset V} (h : Triangle a b c) :
    Triangle b a c := by
  obtain ⟨x,y,z,xy,xz,yz,rfl,rfl,rfl⟩ := h
  exact ⟨z,y,x,Ne.symm yz,Ne.symm xz,Ne.symm xy,
    pair_comm _ _,pair_comm _ _,pair_comm _ _⟩

theorem ordered_triangle {G : Finset (Finset V)} {a b c : Finset V}
    (h : {a,b,c}∈graphTriangles G) : Triangle a b c := by
  have H := (mem_graphTriangles.mp h).2
  obtain ⟨x,y,z,tx,eq⟩ := H.2
  have noPair (v w : Finset V) : ({v,w}:Finset (Finset V)).card≠3 := by
    by_cases e : v=w <;> simp [e]
  have ab : a≠b := by intro e; subst b; exact noPair a c (by simpa using H.1)
  have ac : a≠c := by intro e; subst c; exact noPair b a (by simpa using H.1)
  have bc : b≠c := by intro e; subst c; exact noPair a b (by simpa using H.1)
  have ma : a=x ∨ a=y ∨ a=z := by
    have hh : a ∈ ({x,y,z} : Finset (Finset V)) := eq ▸ mem_insert_self a {b,c}
    simpa using hh
  have mb : b=x ∨ b=y ∨ b=z := by
    have hh : b ∈ ({x,y,z} : Finset (Finset V)) := eq ▸ (by simp : b∈({a,b,c}:Finset (Finset V)))
    simpa using hh
  have mc : c=x ∨ c=y ∨ c=z := by
    have hh : c ∈ ({x,y,z} : Finset (Finset V)) := eq ▸ (by simp : c∈({a,b,c}:Finset (Finset V)))
    simpa using hh
  rcases ma with rfl|rfl|rfl <;> rcases mb with rfl|rfl|rfl <;>
    rcases mc with rfl|rfl|rfl <;> try contradiction
  all_goals first | exact tx | exact triangle_flip tx | exact triangle_rotate tx |
      exact triangle_rotate (triangle_rotate tx) | exact triangle_flip (triangle_rotate tx) |
      exact triangle_flip (triangle_rotate (triangle_rotate tx))

def HasLineFragment (S : Finset (Finset (Finset V))) : Prop :=
  ∃ w : Fin 7 → Finset V, (∀ i, (w i).card=2) ∧
    {w 0,w 3,w 4}∈S ∧ {w 0,w 5,w 6}∈S ∧ {w 1,w 3,w 5}∈S ∧
    {w 1,w 4,w 6}∈S ∧ {w 2,w 3,w 6}∈S ∧ {w 2,w 4,w 5}∈S

def HasPointFragment (S : Finset (Finset (Finset V))) : Prop :=
  ∃ w : Fin 7 → Finset V, (∀ i, (w i).card=2) ∧
    {w 0,w 1,w 2}∈S ∧ {w 0,w 3,w 4}∈S ∧ {w 1,w 3,w 5}∈S ∧
    {w 2,w 4,w 5}∈S ∧ {w 0,w 5,w 6}∈S

theorem no_triangle_fano_fragments {G S : Finset (Finset (Finset V))}
    (_h : S⊆G) (actual : ∀ t∈S, ∃ a b c, Triangle a b c ∧ t={a,b,c})
    (card3 : ∀ t∈S, t.card=3) :
    ¬ (HasLineFragment S ∨ HasPointFragment S) := by
  classical
  let edges := S.biUnion id
  have incl : S⊆graphTriangles edges := by
    intro t ts
    exact mem_graphTriangles.mpr ⟨fun e he => mem_biUnion.mpr ⟨t,ts,he⟩,
      card3 t ts,actual t ts⟩
  rintro (⟨w,wc,a,b,c,d,e,f⟩|⟨w,wc,a,b,c,d,e⟩)
  · exact graph_deleted_line_impossible w wc (ordered_triangle (incl a))
      (ordered_triangle (incl b)) (ordered_triangle (incl c)) (ordered_triangle (incl d))
      (ordered_triangle (incl e)) (ordered_triangle (incl f))
  · exact graph_deleted_point_impossible w wc (ordered_triangle (incl a))
      (ordered_triangle (incl b)) (ordered_triangle (incl c)) (ordered_triangle (incl d))
      (ordered_triangle (incl e))

theorem graph_no_fano {G : Finset (Finset V)} {S : Finset (Finset (Finset V))}
    (hs : S⊆graphTriangles G) : ¬ (HasLineFragment S ∨ HasPointFragment S) :=
  no_triangle_fano_fragments hs (fun _ ht => (mem_graphTriangles.mp (hs ht)).2.2)
    (fun _ ht => (mem_graphTriangles.mp (hs ht)).2.1)

#print axioms graph_no_fano
end FolkmanB4
