import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation

namespace WagnerBypass

variable {V : Type*}

/-- Restrict edges to a vertex set without changing the ambient vertex type. -/
def restrict (R : V → V → Prop) (ok : V → Prop) (x y : V) : Prop :=
  R x y ∧ ok x ∧ ok y

/-- A connection in the graph after excluding previously forbidden vertices
can be made to avoid one more vertex, provided its surviving neighbors can
all reach one another without it. -/
theorem bypass_one (R : V → V → Prop) (ok : V → Prop) (z a b : V)
    (ha : a ≠ z) (hb : b ≠ z)
    (connect_link : ∀ x y, R x z → R z y → ok x → ok y → x ≠ z → y ≠ z →
      Relation.ReflTransGen (restrict R (fun v => ok v ∧ v ≠ z)) x y)
    (walk : Relation.ReflTransGen (restrict R ok) a b) :
    Relation.ReflTransGen (restrict R (fun v => ok v ∧ v ≠ z)) a b := by
  classical
  let Q := restrict R (fun v => ok v ∧ v ≠ z)
  have convert {w : V} (h : Relation.ReflTransGen (restrict R ok) a w) :
      (w ≠ z → Relation.ReflTransGen Q a w) ∧
      (w = z → ∃ x, Relation.ReflTransGen Q a x ∧ R x z ∧ ok x ∧ x ≠ z) := by
    induction h with
    | refl => exact ⟨fun _ => .refl, fun h => (ha h).elim⟩
    | @tail c w old step ih =>
      obtain ⟨hcw, hc, hw⟩ := step
      by_cases hcz : c = z
      · obtain ⟨x, hx, hxz, hok, hn⟩ := ih.2 hcz
        constructor
        · intro hwz
          exact hx.trans (connect_link x w hxz (hcz ▸ hcw) hok hw hn hwz)
        · exact fun _ => ⟨x, hx, hxz, hok, hn⟩
      · have H := ih.1 hcz
        constructor
        · intro hwz
          exact .tail H ⟨hcw, ⟨hc, hcz⟩, ⟨hw, hwz⟩⟩
        · intro hwz
          exact ⟨c, H, hwz ▸ hcw, hc, hcz⟩
  exact (convert walk).1 hb

/-- Repeated bypass turns local connectivity after at most two other
deletions into global connectivity after at most three deletions. -/
theorem avoid_three [DecidableEq V] (R : V → V → Prop)
    (connected : ∀ x y : V, Relation.ReflTransGen R x y)
    (link : ∀ z : V, ∀ S : Finset V, S.card ≤ 2 →
      ∀ x y, R x z → R z y → x ∉ S → y ∉ S → x ≠ z → y ≠ z →
      Relation.ReflTransGen (restrict R (fun v => v ∉ S ∧ v ≠ z)) x y)
    (S : Finset V) (hS : S.card ≤ 3)
    (a b : V) (ha : a ∉ S) (hb : b ∉ S) :
    Relation.ReflTransGen (restrict R (fun v => v ∉ S)) a b := by
  classical
  revert hS a b ha hb
  induction S using Finset.induction_on with
  | empty =>
    intro _ a b _ _
    exact @Relation.ReflTransGen.mono V R (restrict R (fun v => v ∉ (∅ : Finset V)))
      (fun _ _ h => ⟨h, by simp, by simp⟩) a b (connected a b)
  | @insert z S hz ih =>
    intro hcard a b ha hb
    have hsmall : S.card ≤ 2 := by
      simp only [Finset.card_insert_of_notMem hz] at hcard
      omega
    have hsa : a ∉ S := fun h => ha (Finset.mem_insert_of_mem h)
    have hsb : b ∉ S := fun h => hb (Finset.mem_insert_of_mem h)
    have haz : a ≠ z := fun h => ha (h ▸ Finset.mem_insert_self z S)
    have hbz : b ≠ z := fun h => hb (h ▸ Finset.mem_insert_self z S)
    have hconn := bypass_one R (fun v => v ∉ S) z a b haz hbz
      (link z S hsmall) (ih (by omega) a b hsa hsb)
    exact @Relation.ReflTransGen.mono V (restrict R (fun v => v ∉ S ∧ v ≠ z))
      (restrict R (fun v => v ∉ insert z S)) (fun x y h => ⟨h.1, by
      simpa only [Finset.mem_insert, not_or, and_comm] using h.2.1, by
      simpa only [Finset.mem_insert, not_or, and_comm] using h.2.2⟩) a b hconn

#print axioms bypass_one
#print axioms avoid_three
end WagnerBypass
