import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Logic.Relation

namespace WagnerFin8
set_option maxRecDepth 50000
set_option maxHeartbeats 0

def Adj (a b : Fin 8) : Prop :=
  (b.val+8-a.val)%8=1 ∨ (b.val+8-a.val)%8=4 ∨ (b.val+8-a.val)%8=7

instance : DecidableRel Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

theorem symmetric : ∀ a b : Fin 8, Adj a b → Adj b a := by
  decide +kernel

theorem irreflexive : ∀ a : Fin 8, ¬ Adj a a := by
  decide +kernel

theorem degree : ∀ a : Fin 8, ((Finset.univ : Finset (Fin 8)).filter (Adj a)).card = 3 := by
  decide +kernel

theorem edge_cut : ∀ U : Finset (Fin 8), 0 < U.card → U.card < 8 →
    3 ≤ ((U ×ˢ (Finset.univ \ U)).filter (fun x => Adj x.1 x.2)).card := by
  decide +kernel

def reach (S : Finset (Fin 8)) (a : Fin 8) : Nat → Finset (Fin 8)
  | 0 => {a}
  | n+1 =>
    let old := reach S a n
    (Finset.univ : Finset (Fin 8)).filter (fun b =>
      b ∉ S ∧ (b ∈ old ∨ (∃ x ∈ old, Adj x b)))

theorem certificate (S : Finset (Fin 8)) (a : Fin 8) (ha : a ∉ S) :
    ∀ n b, b ∈ reach S a n →
      b ∉ S ∧ Relation.ReflTransGen (fun x y => Adj x y ∧ x ∉ S ∧ y ∉ S) a b := by
  intro n
  induction n with
  | zero =>
    intro b h
    have : b=a := Finset.mem_singleton.mp h
    subst b
    exact ⟨ha,.refl⟩
  | succ n ih =>
    intro b h
    change b ∈ Finset.univ.filter _ at h
    obtain ⟨hb,hc⟩ := (Finset.mem_filter.mp h).2
    refine ⟨hb,?_⟩
    rcases hc with hc | hx
    · exact (ih b hc).2
    · obtain ⟨x, hxn, hxb⟩ := hx
      exact .tail (ih x hxn).2 ⟨hxb,(ih x hxn).1,hb⟩

private theorem reach_check : ∀ S : Finset (Fin 8), S.card ≤ 2 →
    ∀ a b : Fin 8, a ∉ S → b ∉ S → b ∈ reach S a 8 := by
  decide +kernel

theorem connected_after_two (S : Finset (Fin 8)) (hS : S.card ≤ 2)
    (a b : Fin 8) (ha : a ∉ S) (hb : b ∉ S) :
    Relation.ReflTransGen (fun x y => Adj x y ∧ x ∉ S ∧ y ∉ S) a b :=
  (certificate S a ha 8 b (reach_check S hS a b ha hb)).2

theorem square : Adj 0 1 ∧ Adj 1 5 ∧ Adj 5 4 ∧ Adj 4 0 := by
  decide +kernel

#print axioms edge_cut
#print axioms connected_after_two
end WagnerFin8
