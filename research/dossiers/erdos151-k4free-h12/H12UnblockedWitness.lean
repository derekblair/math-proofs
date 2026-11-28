import H12AdjacentPrice

namespace Erdos151H12
open Erdős151

variable {V : Type*} (G : V → V → Prop)

theorem unblocked_both_nonLone_common
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (S : Set V) (u v : V) (hne : u ≠ v)
    (hu : Free (Forbidden G) (insert u S)) (hv : Free (Forbidden G) (insert v S))
    (hb : ¬ Free (Forbidden G) (insert u (insert v S))) (hl : ¬ Lone G u v) :
    ∃ x ∈ S, G u x ∧ G v x := by
  classical
  unfold Free at hb
  push_neg at hb
  obtain ⟨A,hA,hs⟩ := hb
  have hua : u ∈ A := by
    by_contra h
    apply hv A hA
    intro a ha
    exact (Set.mem_insert_iff.mp (hs ha)).resolve_left (fun e => h (e ▸ ha))
  have hva : v ∈ A := by
    by_contra h
    apply hu A hA
    intro a ha
    rcases Set.mem_insert_iff.mp (hs ha) with e | he
    · exact Set.mem_insert_iff.mpr (Or.inl e)
    · rcases Set.mem_insert_iff.mp he with e | he
      · exact False.elim (h (e ▸ ha))
      · exact Set.mem_insert_iff.mpr (Or.inr he)
  rcases hA with ⟨a,b,rfl,hab⟩ | ⟨a,b,c,rfl,hab,hbc,hac⟩
  · simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hua hva
    rcases hua with rfl|rfl <;> rcases hva with rfl|rfl
    · exact False.elim (hne rfl)
    · exact False.elim (hl hab)
    · exact False.elim (hl ⟨sym hab.1,fun x hx => hab.2 x ⟨hx.2,hx.1⟩⟩)
    · exact False.elim (hne rfl)
  · have th : ∃ x ∈ ({a,b,c} : Set V), x ≠ u ∧ x ≠ v := by
      by_contra! nh
      have ah : a = u ∨ a = v := by
        by_cases eq : a = u
        · exact Or.inl eq
        · exact Or.inr (nh a (by simp) eq)
      have bh : b = u ∨ b = v := by
        by_cases eq : b = u
        · exact Or.inl eq
        · exact Or.inr (nh b (by simp) eq)
      have ch : c = u ∨ c = v := by
        by_cases eq : c = u
        · exact Or.inl eq
        · exact Or.inr (nh c (by simp) eq)
      rcases ah with rfl|rfl <;> rcases bh with rfl|rfl <;> rcases ch with rfl|rfl
      all_goals first | exact irr _ hab | exact irr _ hbc | exact irr _ hac
    obtain ⟨x,hx,hxu,hxv⟩ := th
    have hmem : x ∈ S := by
      have h := hs hx
      simpa [Set.mem_insert_iff,hxu,hxv] using h
    have hForb : Forbidden G {a,b,c} := Or.inr ⟨a,b,c,rfl,hab,hbc,hac⟩
    exact ⟨x,hmem,forbidden_clique G sym _ hForb u x hua hx hxu.symm,
      forbidden_clique G sym _ hForb v x hva hx hxv.symm⟩

/-- An unblocked exterior triangle consumes at least two ambient incidences per vertex. -/
theorem unblocked_triangle_two_neighbors [DecidableEq V] [DecidableRel G]
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) (tf : TriangleFreeLinks G)
    (S : Finset V) (u v w : V) (huv : u ≠ v) (huw : u ≠ w)
    (uv : G u v) (uw : G u w) (vw : G v w)
    (hu : Free (Forbidden G) (insert u (S : Set V)))
    (hv : Free (Forbidden G) (insert v (S : Set V)))
    (hw : Free (Forbidden G) (insert w (S : Set V)))
    (buv : ¬ Free (Forbidden G) (insert u (insert v (S : Set V))))
    (buw : ¬ Free (Forbidden G) (insert u (insert w (S : Set V)))) :
    2 ≤ (S.filter (G u)).card := by
  obtain ⟨x,hx,hux,hvx⟩ := unblocked_both_nonLone_common G sym irr _ u v huv hu hv buv
    (fun h => h.2 w ⟨uw,vw⟩)
  obtain ⟨y,hy,huy,hwy⟩ := unblocked_both_nonLone_common G sym irr _ u w huw hu hw buw
    (fun h => h.2 v ⟨uv,sym vw⟩)
  have hne : x ≠ y := by
    intro e
    subst y
    exact tf x u v w (sym hux) (sym hvx) (sym hwy) uv vw uw
  have hsub : ({x,y} : Finset V) ⊆ S.filter (G u) := by
    exact Finset.insert_subset_iff.mpr
      ⟨Finset.mem_filter.mpr ⟨hx,hux⟩,Finset.singleton_subset_iff.mpr (Finset.mem_filter.mpr ⟨hy,huy⟩)⟩
  have hcard := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem (by simpa only [Finset.mem_singleton] using hne),
      Finset.card_singleton] at hcard

#print axioms unblocked_both_nonLone_common
#print axioms unblocked_triangle_two_neighbors
end Erdos151H12
