import GraphBookCore

namespace FolkmanB4
open Finset Critical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact structural input still required: a nonempty cubic triangle
incidence system with constant perfect matching parity contains a Fano
fragment. The paper derives this by tight cuts and Pfaffian braces. -/
def StructuralInput (V : Type*) [Fintype V] [DecidableEq V] : Prop :=
  ∀ S : Finset (Finset (Finset V)), S.Nonempty →
    (∀ t : Line S, pts (inc S) t=3) →
    (∀ e : Point S, lns (inc S) e=3) →
    (∀ e : Point S, e.val.card=2) →
    (∃ k : Point S ≃ Line S,
        ∀ s t : Point S ≃ Line S, (∀ i, inc S (s i) i) → (∀ i, inc S (t i) i) →
          pSign (s.trans k.symm)=pSign (t.trans k.symm)) →
    HasLineFragment S ∨ HasPointFragment S

theorem graph_color_of_structure (G : Finset (Finset V)) (book : BookFree G)
    (shape : StructuralInput V) : Splittable (graphTriangles G) := by
  classical
  by_contra bad
  obtain ⟨S,sub,ne,rows,cols,parity⟩ :=
    family_core (fun t ht => (mem_graphTriangles.mp ht).2.1) book bad
  have edges (e : Point S) : e.val.card=2 := by
    obtain ⟨t,ht,he⟩ := mem_points.mp e.property
    obtain ⟨a,b,c,h,eq⟩ := (mem_graphTriangles.mp (sub ht)).2.2
    rw [eq] at he
    obtain ⟨x,y,z,xy,xz,yz,rfl,rfl,rfl⟩ := h
    simp only [mem_insert,mem_singleton] at he
    rcases he with h|h|h <;> rw [h] <;> simp [xy,xz,yz,Ne.symm xz]
  exact graph_no_fano sub (shape S ne rows cols edges parity)

#print axioms graph_color_of_structure
end FolkmanB4
