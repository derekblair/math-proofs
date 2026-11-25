import Result

open SimpleGraph
open scoped BigOperators
namespace Refute269

/-- Four portals, any number of four-vertex tracks, and any number of two-vertex tracks. -/
abbrev Vert (m n : Nat) := Fin 4 ⊕ ((Fin m × Fin 4) ⊕ (Fin n × Fin 2))
abbrev P {m n : Nat} (i : Fin 4) : Vert m n := .inl i
abbrev A {m n : Nat} (i : Fin m) (r : Fin 4) : Vert m n := .inr (.inl (i,r))
abbrev B {m n : Nat} (i : Fin n) (r : Fin 2) : Vert m n := .inr (.inr (i,r))

def portEdges (r s : Fin 4) : Prop :=
  (r = 0 ∧ s = 1) ∨ (r = 1 ∧ s = 0) ∨ (r = 2 ∧ s = 3) ∨ (r = 3 ∧ s = 2)
def trackEdges (r s : Fin 4) : Prop :=
  (r = 0 ∧ s = 1) ∨ (r = 1 ∧ s = 0) ∨ (r = 0 ∧ s = 2) ∨ (r = 2 ∧ s = 0)
    ∨ (r = 1 ∧ s = 3) ∨ (r = 3 ∧ s = 1)
def ap (r : Fin 4) : Fin 4 := if r = 0 ∨ r = 2 then 0 else 3
def bp (r : Fin 2) : Fin 4 := if r = 0 then 1 else 2

def adj {m n : Nat} : Vert m n → Vert m n → Prop
  | .inl r, .inl s => portEdges r s
  | .inl r, .inr (.inl (_,s)) => r = ap s
  | .inr (.inl (_,s)), .inl r => r = ap s
  | .inl r, .inr (.inr (_,s)) => r = bp s
  | .inr (.inr (_,s)), .inl r => r = bp s
  | .inr (.inl (i,r)), .inr (.inl (j,s)) => i = j ∧ trackEdges r s
  | .inr (.inr (i,r)), .inr (.inr (j,s)) => i = j ∧ r ≠ s
  | _, _ => False

instance {m n : Nat} (v w : Vert m n) : Decidable (adj v w) := by
  rcases v with p | (⟨i,r⟩ | ⟨i,r⟩) <;> rcases w with q | (⟨j,s⟩ | ⟨j,s⟩) <;>
    simp only [adj, trackEdges, portEdges] <;> infer_instance

lemma portSymm : ∀ r s, portEdges r s ↔ portEdges s r := by
  intro r s
  unfold portEdges
  tauto
lemma trackSymm : ∀ r s, trackEdges r s ↔ trackEdges s r := by
  intro r s
  unfold trackEdges
  tauto

def graph (m n : Nat) : SimpleGraph (Vert m n) where
  Adj := adj
  symm := by
    constructor
    intro v w h
    rcases v with p | (⟨i,r⟩ | ⟨i,r⟩) <;> rcases w with q | (⟨j,s⟩ | ⟨j,s⟩) <;>
      simp only [adj] at h ⊢
    all_goals first | exact h | exact (portSymm _ _).mp h |
      exact ⟨h.1.symm, (trackSymm _ _).mp h.2⟩ | exact ⟨h.1.symm, Ne.symm h.2⟩
  loopless := by
    constructor
    intro v
    rcases v with p | (⟨i,r⟩ | ⟨i,r⟩) <;>
      simp only [adj, portEdges, trackEdges] <;> omega

instance (m n : Nat) : DecidableRel (graph m n).Adj := fun v w => inferInstanceAs (Decidable (adj v w))

def reindex {m n m' n' : Nat} (f : Fin m → Fin m') (g : Fin n → Fin n') :
    graph m n →g graph m' n' where
  toFun
    | .inl r => P r
    | .inr (.inl (i,r)) => A (f i) r
    | .inr (.inr (i,r)) => B (g i) r
  map_rel' := by
    intro v w h
    change adj v w at h
    rcases v with p | (⟨i,r⟩ | ⟨i,r⟩) <;> rcases w with q | (⟨j,s⟩ | ⟨j,s⟩) <;>
      first | exact h | exact ⟨congrArg f h.1, h.2⟩ | exact ⟨congrArg g h.1, h.2⟩

-- Graph distance for a chosen pair depends only on the role of each endpoint and
-- whether the two track indices agree. All unused indices may be collapsed.
def color {m : Nat} (anchor : Fin m) (i : Fin m) : Fin 2 := if i = anchor then 0 else 1
def pick {m : Nat} (a b : Fin m) (x : Fin 2) : Fin m := if x = 0 then a else b

lemma pick_anchor {m : Nat} (a b : Fin m) : pick a b (color a a) = a := by simp [pick,color]
lemma pick_other {m : Nat} (a b : Fin m) : pick a b (color a b) = b := by
  by_cases h : b = a <;> simp [pick,color,h]

#print axioms graph
#print axioms reindex
end Refute269
