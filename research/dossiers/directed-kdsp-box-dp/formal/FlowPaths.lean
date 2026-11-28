import Mathlib.Logic.Relation
import Mathlib.Data.Nat.Init

namespace DirectedBoxDSP

variable {V : Type*}

/-- In an acyclic roster, every active vertex traces back to the
source given the existence of an incoming arc at every other active vertex.
No encoding of which ports are paired is needed at a merge. -/
theorem reaches_from_source
    (arc : V → V → Prop) (active : V → Prop) (rank : V → ℕ) (s : V)
    (strict : ∀ u v, arc u v → rank u < rank v)
    (incoming : ∀ v, active v → v ≠ s → ∃ u, active u ∧ arc u v) :
    ∀ v, active v → Relation.ReflTransGen arc s v := by
  have hp (n : ℕ) : ∀ v, rank v = n → active v → Relation.ReflTransGen arc s v := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hva hv
      by_cases hvs : v = s
      · subst v
        exact Relation.ReflTransGen.refl
      · obtain ⟨u, hu, huv⟩ := incoming v hv hvs
        have hlt : rank u < n := hva ▸ strict u v huv
        exact (ih (rank u) hlt u rfl hu).tail huv
  intro v hv
  exact hp (rank v) v rfl hv

/-- With incoming and outgoing constraints and a bounded increasing rank,
each selected arc lies on a source–sink walk. Strict rank makes the walk
acyclic. This rules out extraneous disconnected flow components. -/
theorem selected_arc_lies_on_route
    (arc : V → V → Prop) (active : V → Prop) (rank : V → ℕ) (s t : V) (N : ℕ)
    (bound : ∀ v, rank v ≤ N)
    (strict : ∀ u v, arc u v → rank u < rank v)
    (support : ∀ u v, arc u v → active u ∧ active v)
    (incoming : ∀ v, active v → v ≠ s → ∃ u, active u ∧ arc u v)
    (outgoing : ∀ u, active u → u ≠ t → ∃ v, active v ∧ arc u v) :
    ∀ u v, arc u v →
      Relation.ReflTransGen arc s u ∧ Relation.ReflTransGen arc v t := by
  have hr := reaches_from_source arc active rank s strict incoming
  have ht := reaches_from_source (fun a b => arc b a) active
    (fun a => N - rank a) t (by
      intro a b h
      have hlt := strict b a h
      have hle := bound a
      omega) outgoing
  intro u v huv
  obtain ⟨hu, hv⟩ := support u v huv
  exact ⟨hr u hu, (Relation.reflTransGen_swap.mp (ht v hv))⟩

#print axioms reaches_from_source
#print axioms selected_arc_lies_on_route
end DirectedBoxDSP
