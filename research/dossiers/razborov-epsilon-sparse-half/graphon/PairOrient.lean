import CountableAnchors

open Set Function
namespace SparseHalfGraphon

/-- Orient a fixed-point-free involution on a countable type using any
embedding in the naturals. Every point belongs to precisely one pair. -/
theorem orient_countable_involution {A : Type*} [Countable A]
    (f : A→A) (hf : Involutive f) (hn : ∀ a, f a≠a) :
    ∃ R : Set A, (∀ a, a∈R ↔ f a∉R) ∧
      (∀ a, a∈R ∨ f a∈R) ∧ R.Countable := by
  letI : Encodable A := Encodable.ofCountable A
  let R : Set A := {a | Encodable.encode a < Encodable.encode (f a)}
  refine ⟨R,?_,?_,Set.to_countable _⟩
  · intro a
    have hne : Encodable.encode a ≠ Encodable.encode (f a) :=
      fun hh => hn a (Encodable.encode_injective hh).symm
    change (Encodable.encode a < Encodable.encode (f a)) ↔
      ¬ (Encodable.encode (f a) < Encodable.encode (f (f a)))
    rw [hf,not_lt]
    exact ⟨le_of_lt,fun h=>lt_of_le_of_ne h hne⟩
  · intro a
    change (Encodable.encode a < Encodable.encode (f a)) ∨
      (Encodable.encode (f a) < Encodable.encode (f (f a)))
    rw [hf]
    exact lt_or_gt_of_ne (fun hh=>hn a (Encodable.encode_injective hh).symm)

#print axioms orient_countable_involution
end SparseHalfGraphon
