import HubSet
import OwnerPath
import Mathlib.Tactic.Tauto

namespace Erdos151H13
open Erdős151 Erdos151H12
variable {V : Type*} [DecidableEq V] (G : V → V → Prop)

def CenterEligible (x w y a : V) : Prop :=
  G w a ∧ ¬ Lone G w a ∧ ¬ G x a ∧ ¬ G y a

def OuterEligible (x w y a : V) : Prop :=
  ¬ G w a ∧ ¬ Lone G x a ∧ ¬ Lone G y a

/-- The exact three-hub insertion can keep a center-independent pool
and an independent set of the outer conflict graph at the same time. -/
theorem safe_insert_induced_path
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (x w y : V) (xy : ¬ G x y) (xw : ¬ Lone G x w) (yw : ¬ Lone G y w)
    (A B T : Set V)
    (hA : ∀ a ∈ A, CenterEligible G x w y a)
    (hB : ∀ a ∈ B, OuterEligible G x w y a)
    (iA : ∀ a ∈ A, ∀ b ∈ A, ¬ G a b)
    (iB : ∀ a ∈ B, ∀ b ∈ B, ¬ pairConflict G x y a b)
    (hT : Free (Forbidden G) T)
    (retained : ∀ a ∈ T, a ∈ A ∨ a ∈ B ∨ (¬ G x a ∧ ¬ G w a ∧ ¬ G y a)) :
    Free (Forbidden G) ((({x,w,y} : Finset V) : Set V) ∪ T) := by
  have hh : Free (Forbidden G) (({x,y} : Set V) ∪ {w}) := by
    apply free_bipartite_unless_lone G sym
    · intro a ha b hb
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
      rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
      · exact irr _
      · exact xy
      · exact fun h => xy (sym h)
      · exact irr _
    · intro a ha b hb
      simp only [Set.mem_singleton_iff] at ha hb
      subst a
      subst b
      exact irr _
    · intro a ha b hb
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
      subst b
      rcases ha with rfl|rfl
      · exact xw
      · exact yw
  have he : (({x,w,y} : Finset V) : Set V) = (({x,y} : Set V) ∪ {w}) := by
    ext a
    simp
    tauto
  apply safe_insert_hubs G sym irr _ _ (he.symm ▸ hh) hT
  · intro h hh a ha H
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    rcases retained a ha with ha|ha|ha
    · have h := hA a ha
      rcases hh with rfl|rfl|rfl
      · exact h.2.2.1 H.1
      · exact h.2.1 H
      · exact h.2.2.2 H.1
    · have h := hB a ha
      rcases hh with rfl|rfl|rfl
      · exact h.2.1 H
      · exact h.1 H.1
      · exact h.2.2 H
    · rcases hh with rfl|rfl|rfl
      · exact ha.1 H.1
      · exact ha.2.1 H.1
      · exact ha.2.2 H.1
  · intro h hh j hj a ha hjh hha hja
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh hj
    rcases retained a ha with ha|ha|ha
    · have u := hA a ha
      have hna (v : V) (hv : v=x ∨ v=w ∨ v=y) (P : G v a) : v=w := by
        rcases hv with rfl|rfl|rfl
        · exact (u.2.2.1 P).elim
        · rfl
        · exact (u.2.2.2 P).elim
      have h1 := hna h hh hha
      have h2 := hna j hj hja
      subst h
      subst j
      exact irr _ hjh
    · have u := hB a ha
      rcases hh with rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl
      all_goals first
        | exact irr _ hjh
        | exact u.1 hha
        | exact u.1 hja
        | exact xy hjh
        | exact xy (sym hjh)
    · rcases hh with rfl|rfl|rfl
      · exact ha.1 hha
      · exact ha.2.1 hha
      · exact ha.2.2 hha
  · intro h hh a ha b hb hha hhb hab
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    have kind (v : V) (hv : v ∈ T) :
        (G x v → v ∈ B) ∧ (G w v → v ∈ A) ∧ (G y v → v ∈ B) := by
      rcases retained v hv with hv|hv|hv
      · have u := hA v hv
        exact ⟨fun e => (u.2.2.1 e).elim, fun _ => hv, fun e => (u.2.2.2 e).elim⟩
      · have u := hB v hv
        exact ⟨fun _ => hv, fun e => (u.1 e).elim, fun _ => hv⟩
      · exact ⟨fun e => (hv.1 e).elim, fun e => (hv.2.1 e).elim, fun e => (hv.2.2 e).elim⟩
    have ka := kind a ha
    have kb := kind b hb
    rcases hh with rfl|rfl|rfl
    · exact iB a (ka.1 hha) b (kb.1 hhb) ⟨hab,Or.inl ⟨hha,hhb⟩⟩
    · exact iA a (ka.2.1 hha) b (kb.2.1 hhb) hab
    · exact iB a (ka.2.2 hha) b (kb.2.2 hhb) ⟨hab,Or.inr ⟨hha,hhb⟩⟩

#print axioms safe_insert_induced_path
end Erdos151H13
