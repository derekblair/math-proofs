import FanoParity

namespace FolkmanB4
open Finset
open scoped BigOperators

/-- A literal triangle with the three specified unordered edges. -/
def Triangle {V : Type*} [DecidableEq V] (A B C : Finset V) : Prop :=
  ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ A = {a,b} ∧ B = {b,c} ∧ C = {c,a}

theorem triangle_even {V : Type*} [DecidableEq V] {A B C : Finset V}
    (h : Triangle A B C) (v : V) :
    even (decide (v∈A)) (decide (v∈B)) (decide (v∈C)) = true := by
  obtain ⟨a,b,c,ab,ac,bc,rfl,rfl,rfl⟩ := h
  by_cases h1 : v=a
  · subst v
    simp [even,ab,ac]
  by_cases h2 : v=b
  · subst v
    simp [even,h1,bc]
  by_cases h3 : v=c
  · subst v
    simp [even,h1,h2]
  · simp [even,h1,h2,h3]

theorem edge_row_weights {V : Type*} [Fintype V] [DecidableEq V]
    (E : Fin 7 → Finset V) (h : ∀ i, (E i).card=2) :
    EdgeWeights (fun i v => decide (v∈E i)) := by
  intro i
  have e (v : V) : (decide (v∈E i)).toNat = if v∈E i then 1 else 0 := by
    by_cases k : v∈E i <;> simp [k]
  simp only [e]
  rw [←sum_filter]
  simpa using h i

theorem graph_deleted_line_impossible {V : Type*} [Fintype V] [DecidableEq V]
    (E : Fin 7 → Finset V) (h : ∀ i, (E i).card=2)
    (a : Triangle (E 0) (E 3) (E 4)) (b : Triangle (E 0) (E 5) (E 6))
    (c : Triangle (E 1) (E 3) (E 5)) (d : Triangle (E 1) (E 4) (E 6))
    (e : Triangle (E 2) (E 3) (E 6)) (f : Triangle (E 2) (E 4) (E 5)) : False := by
  apply deleted_line_impossible _ (edge_row_weights E h)
  intro v
  simp [triangle_even a v, triangle_even b v, triangle_even c v,
    triangle_even d v, triangle_even e v, triangle_even f v]

theorem graph_deleted_point_impossible {V : Type*} [Fintype V] [DecidableEq V]
    (E : Fin 7 → Finset V) (h : ∀ i, (E i).card=2)
    (a : Triangle (E 0) (E 1) (E 2)) (b : Triangle (E 0) (E 3) (E 4))
    (c : Triangle (E 1) (E 3) (E 5)) (d : Triangle (E 2) (E 4) (E 5))
    (e : Triangle (E 0) (E 5) (E 6)) : False := by
  apply deleted_point_impossible _ (edge_row_weights E h)
  intro v
  simp [triangle_even a v, triangle_even b v, triangle_even c v,
    triangle_even d v, triangle_even e v]

#print axioms graph_deleted_line_impossible
#print axioms graph_deleted_point_impossible
end FolkmanB4
