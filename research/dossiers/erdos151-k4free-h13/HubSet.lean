import H12PairInsert

namespace Erdos151H13
open Erdős151 Erdos151H12

variable {V : Type*} [DecidableEq V] (G : V → V → Prop)

/-- A free set of hubs can be inserted together when ordinary retained
vertices do not form a mixed lone edge or mixed triangle. In particular
edges between different kept pools need not be deleted when the pools
do not share a hub. -/
theorem safe_insert_hubs
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (H : Finset V) (T : Set V)
    (hH : Free (Forbidden G) (H : Set V)) (hT : Free (Forbidden G) T)
    (hl : ∀ h ∈ H, ∀ a ∈ T, ¬ Lone G h a)
    (hht : ∀ h ∈ H, ∀ j ∈ H, ∀ a ∈ T, G h j → G h a → ¬ G j a)
    (htt : ∀ h ∈ H, ∀ a ∈ T, ∀ b ∈ T, G h a → G h b → ¬ G a b) :
    Free (Forbidden G) ((H : Set V) ∪ T) := by
  induction H using Finset.induction_on with
  | empty => simpa using hT
  | @insert h U h_not ih =>
    have hh : h ∈ insert h U := Finset.mem_insert_self _ _
    have sub : U ⊆ insert h U := fun a ha => Finset.mem_insert_of_mem ha
    have hU : Free (Forbidden G) (U : Set V) :=
      fun X hX hsub => hH X hX (fun a ha => sub (hsub ha))
    have old := ih hU
      (fun j hj => hl j (sub hj))
      (fun j hj k hk => hht j (sub hj) k (sub hk))
      (fun j hj => htt j (sub hj))
    rw [Finset.coe_insert, Set.insert_union]
    apply safe_insert_one G sym irr _ h old
    · intro a ha hlone
      rcases (Set.mem_union _ _ _).mp ha with ha|ha
      · exact hH {h,a} (Or.inl ⟨h,a,rfl,hlone⟩) (by
          intro j hj
          rcases Set.mem_insert_iff.mp hj with rfl|rfl
          · exact hh
          · exact sub ha)
      · exact hl h hh a ha hlone
    · intro a ha b hb hha hhb hab
      rcases (Set.mem_union _ _ _).mp ha with ha|ha <;>
        rcases (Set.mem_union _ _ _).mp hb with hb|hb
      · exact hH {h,a,b} (Or.inr ⟨h,a,b,rfl,hha,hab,hhb⟩) (by
          intro j hj
          simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hj
          rcases hj with rfl|rfl|rfl
          · exact hh
          · exact sub ha
          · exact sub hb)
      · exact hht h hh a (sub ha) b hb hha hhb hab
      · exact hht h hh b (sub hb) a ha hhb hha (sym hab)
      · exact htt h hh a ha b hb hha hhb hab

#print axioms safe_insert_hubs
end Erdos151H13
