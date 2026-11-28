import H12SaturatedStar
import Mathlib.Tactic.Tauto

namespace Erdos151H13
open Erdős151 Erdos151H12
variable {V : Type*} (G : V → V → Prop)

theorem free_anticomplete_union
    (sym : ∀ {a b}, G a b → G b a) (S A : Set V)
    (hS : Free (Forbidden G) S) (hA : Free (Forbidden G) A)
    (cross : ∀ a ∈ A, ∀ b ∈ S, ¬ G a b) :
    Free (Forbidden G) (A ∪ S) := by
  classical
  intro U hU sub
  by_cases hs : U ⊆ S
  · exact hS U hU hs
  by_cases ha : U ⊆ A
  · exact hA U hU ha
  have ex : ∃ a ∈ U, a ∉ S := by
    by_contra! nh
    exact hs nh
  have ey : ∃ b ∈ U, b ∉ A := by
    by_contra! nh
    exact ha nh
  obtain ⟨a,hau,has⟩ := ex
  obtain ⟨b,hbu,hba⟩ := ey
  have haa := ((Set.mem_union _ _ _).mp (sub hau)).resolve_right has
  have hbs := ((Set.mem_union _ _ _).mp (sub hbu)).resolve_left hba
  have hab : a ≠ b := fun e => has (e ▸ hbs)
  exact cross a haa b hbs (forbidden_clique G sym U hU a b hau hbu hab)

theorem free_bipartite_unless_lone
    (sym : ∀ {a b}, G a b → G b a) (A B : Set V)
    (left : ∀ a ∈ A, ∀ b ∈ A, ¬ G a b)
    (right : ∀ a ∈ B, ∀ b ∈ B, ¬ G a b)
    (cross : ∀ a ∈ A, ∀ b ∈ B, ¬ Lone G a b) :
    Free (Forbidden G) (A ∪ B) := by
  intro U hU sub
  rcases hU with ⟨x,y,rfl,hl⟩ | ⟨x,y,z,rfl,hxy,hyz,hxz⟩
  · rcases (Set.mem_union _ _ _).mp (sub (by simp : x ∈ ({x,y} : Set V))) with hx|hx
    · rcases (Set.mem_union _ _ _).mp (sub (by simp : y ∈ ({x,y} : Set V))) with hy|hy
      · exact left x hx y hy hl.1
      · exact cross x hx y hy hl
    · rcases (Set.mem_union _ _ _).mp (sub (by simp : y ∈ ({x,y} : Set V))) with hy|hy
      · exact cross y hy x hx (lone_symm G sym hl)
      · exact right x hx y hy hl.1
  · rcases (Set.mem_union _ _ _).mp (sub (by simp : x ∈ ({x,y,z} : Set V))) with hx|hx <;>
      rcases (Set.mem_union _ _ _).mp (sub (by simp : y ∈ ({x,y,z} : Set V))) with hy|hy <;>
      rcases (Set.mem_union _ _ _).mp (sub (by simp : z ∈ ({x,y,z} : Set V))) with hz|hz
    all_goals first
      | exact left x hx y hy hxy
      | exact left x hx z hz hxz
      | exact left y hy z hz hyz
      | exact right x hx y hy hxy
      | exact right x hx z hz hxz
      | exact right y hy z hz hyz

/-- With two marked end owners and a common center, the two leaves and
two double-lone columns form a four-for-three swap unless at least one
of the three possible path edges is lone. -/
theorem path_exchange_has_lone [DecidableEq V]
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (R : Finset V) (u v x y : V)
    (hvx : ¬ G v x) (huy : ¬ G u y) (hxy : ¬ G x y)
    (antic : ∀ a ∈ ({u,v,x,y} : Finset V), ∀ b ∈ R, ¬ G a b)
    (rf : Free (Forbidden G) (R : Set V))
    (hsize : 13 ≤ (({u,v,x,y} : Finset V) ∪ R).card)
    (no : ∀ T : Finset V, 13 ≤ T.card → ¬ Free (Forbidden G) (T : Set V)) :
    Lone G u v ∨ Lone G u x ∨ Lone G v y := by
  classical
  by_contra! hn
  have hpair (a b : V) (hab : ¬ G a b) : ∀ i ∈ ({a,b} : Set V), ∀ j ∈ ({a,b} : Set V), ¬ G i j := by
    intro i hi j hj
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hi hj
    rcases hi with rfl|rfl <;> rcases hj with rfl|rfl
    · exact irr _
    · exact hab
    · exact fun h => hab (sym h)
    · exact irr _
  have hfree : Free (Forbidden G) (({u,y} : Set V) ∪ {v,x}) := by
    apply free_bipartite_unless_lone G sym _ _ (hpair u y huy) (hpair v x hvx)
    intro i hi j hj
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hi hj
    rcases hi with rfl|rfl <;> rcases hj with rfl|rfl
    · exact hn.1
    · exact hn.2.1
    · exact fun h => hn.2.2 (lone_symm G sym h)
    · exact fun h => hxy (sym h.1)
  have heq : (({u,v,x,y} : Finset V) : Set V) = (({u,y} : Set V) ∪ {v,x}) := by
    ext a
    simp
    tauto
  apply no (({u,v,x,y} : Finset V) ∪ R) hsize
  rw [Finset.coe_union]
  exact free_anticomplete_union G sym _ _ rf (heq.symm ▸ hfree) antic

#print axioms path_exchange_has_lone
end Erdos151H13
