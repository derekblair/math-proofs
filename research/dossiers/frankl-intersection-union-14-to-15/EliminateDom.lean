import EliminateRows

namespace IU.Eliminate

def Dominates (n b a : Nat) : Prop :=
  rank a n = rank b n ∧ ∀ t ∈ List.range (n+1), rank a t ≤ rank b t

instance (n b a : Nat) : Decidable (Dominates n b a) := by
  unfold Dominates
  infer_instance

theorem edge_mono {n p q a b u : Nat}
    (d : Dominates n u a) (e : edge n p q a b=true) :
    edge n p q u b=true := by
  unfold edge at *
  rw [List.any_eq_true] at e ⊢
  obtain ⟨t,ht,z⟩ := e
  refine ⟨t,ht,?_⟩
  rw [decide_eq_true_eq] at z ⊢
  rw [←d.1]
  exact z.trans (Nat.add_le_add_right (d.2 t ht) _)

theorem certificate_of_dom {k m n p q a : Nat} {colors : Fin k → List Nat}
    {stamp fine : Nat → Nat} {row : Row k}
    (cert : rowOk n p q m colors stamp row)
    (d : Dominates n row.a a)
    (order : ∀ b, b≠a → fine a≤fine b → b≠row.a ∧ stamp row.a≤stamp b) :
    ∃ miss : Finset (Fin k), k - miss.card < m ∧
      ∀ i∈miss, ∀ b∈colors i, b≠a → fine a≤fine b → edge n p q a b=false := by
  obtain ⟨M,count,safe⟩ := from_row rfl cert
  refine ⟨M,count,?_⟩
  intro i im b bc nb ord
  obtain ⟨ne,ord'⟩ := order b nb ord
  have bad := safe i im b bc ne ord'
  by_contra no
  have yes : edge n p q a b=true := Bool.eq_true_of_not_eq_false no
  rw [edge_mono d yes] at bad
  contradiction

end IU.Eliminate
