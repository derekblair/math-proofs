import H12SaturatedStar

namespace Erdos151H13
open Erdős151 Erdos151H12

variable {V : Type*} [DecidableEq V]
variable (G : V → V → Prop)

/-- Adjoining two anticomplete-to-base vertices is safe whenever their only
possible internal edge is not lone. -/
theorem optional_pair_safe
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (T : Set V) (u v : V) (hT : Free (Forbidden G) T)
    (hu : ∀ x ∈ T, ¬ G u x) (hv : ∀ x ∈ T, ¬ G v x)
    (h : ¬ Lone G u v) : Free (Forbidden G) (insert u (insert v T)) := by
  have hV : Free (Forbidden G) (insert v T) := by
    apply safe_insert_one G sym irr _ _ hT
    · exact fun x hx H => hv x hx H.1
    · exact fun x hx _ _ H => (hv x hx H).elim
  apply safe_insert_one G sym irr _ _ hV
  · intro x hx H
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact h H
    · exact hu x hx H.1
  · intro x hx y hy hux huy
    have hxv : x = v := (Set.mem_insert_iff.mp hx).resolve_right (fun hx => hu x hx hux)
    have hyv : y = v := (Set.mem_insert_iff.mp hy).resolve_right (fun hy => hu y hy huy)
    subst x
    subst y
    exact irr v

/-- Replacing owner vertices by a larger family with only one possible
forbidden edge forces that edge to be lone. Applies to an owner-pair
exchange and to an owner-triangle exchange alike. -/
theorem force_lone_exchange
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (R X : Finset V) (u v : V) (m : ℕ)
    (hR : Free (Forbidden G) (R : Set V))
    (hXX : ∀ a ∈ X, ∀ b ∈ X, ¬ G a b)
    (hXR : ∀ a ∈ X, ∀ b ∈ R, ¬ G a b)
    (hu : ∀ x ∈ X ∪ R, ¬ G u x) (hv : ∀ x ∈ X ∪ R, ¬ G v x)
    (huv : u ≠ v) (hu' : u ∉ X ∪ R) (hv' : v ∉ X ∪ R)
    (size : m ≤ (X ∪ R).card + 2)
    (no : ∀ T : Finset V, m ≤ T.card → ¬ Free (Forbidden G) (T : Set V)) :
    Lone G u v := by
  by_contra hl
  have hbase := free_adjoin_independent G sym irr R X hR hXX hXR
  have hup : ∀ a ∈ (↑(X ∪ R) : Set V), ¬ G u a := hu
  have hvp : ∀ a ∈ (↑(X ∪ R) : Set V), ¬ G v a := hv
  have hall := optional_pair_safe G sym irr (↑(X ∪ R) : Set V) u v hbase hup hvp hl
  let T := insert u (insert v (X ∪ R))
  have hsize : m ≤ T.card := by
    unfold T
    rw [Finset.card_insert_of_notMem (fun h => (Finset.mem_insert.mp h).elim huv hu'),
        Finset.card_insert_of_notMem hv']
    omega
  exact no T hsize (by simpa [T,Finset.coe_insert] using hall)

#print axioms optional_pair_safe
#print axioms force_lone_exchange
end Erdos151H13
