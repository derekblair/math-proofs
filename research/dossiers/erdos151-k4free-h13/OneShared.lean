import RamseySmall

namespace Erdos151H13
open Erdos151Ramsey

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : V → V → Prop) [DecidableRel G]

theorem pick_two (S : Finset V) (h : 2 ≤ S.card) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b := by
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0<S.card by omega)
  have e := Finset.card_erase_add_one ha
  obtain ⟨b,hb⟩ := Finset.card_pos.mp (show 0<(S.erase a).card by omega)
  obtain ⟨ne,hb⟩ := Finset.mem_erase.mp hb
  exact ⟨a,ha,b,hb,ne.symm⟩

theorem independent_single (irr : ∀ a, ¬ G a a) (a : V) :
    Independent G ({a} : Finset V) := by
  intro x hx y hy
  simp only [Finset.mem_singleton] at hx hy
  subst x
  subst y
  exact irr _

/-- In a triangle-free conflict graph, two anticomplete two-vertex
pools plus one shared site always give an independent triple. -/
theorem independent_three_one_shared
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (tf : TriangleFree G) (A B : Finset V) (p : V)
    (a2 : 2 ≤ A.card) (b2 : 2 ≤ B.card)
    (pa : p ∉ A) (pb : p ∉ B) (dis : Disjoint A B)
    (cross : ∀ a ∈ A, ∀ b ∈ B, ¬ G a b) :
    ∃ X ⊆ insert p (A ∪ B), 3 ≤ X.card ∧ Independent G X := by
  obtain ⟨a,ha,a',ha',naa⟩ := pick_two A a2
  obtain ⟨b,hb,b',hb',nbb⟩ := pick_two B b2
  have mk (u v z : V) (uv : u ≠ v) (uz : u ≠ z) (vz : v ≠ z)
      (hu : u ∈ insert p (A ∪ B)) (hv : v ∈ insert p (A ∪ B))
      (hz : z ∈ insert p (A ∪ B))
      (nuv : ¬ G u v) (nuz : ¬ G u z) (nvz : ¬ G v z) :
      ∃ X ⊆ insert p (A ∪ B), 3 ≤ X.card ∧ Independent G X := by
    refine ⟨{u,v,z}, Finset.insert_subset_iff.mpr ⟨hu,Finset.insert_subset_iff.mpr
      ⟨hv,Finset.singleton_subset_iff.mpr hz⟩⟩, ?_,?_⟩
    · rw [Finset.card_insert_of_notMem (by simp [uv,uz]),
          Finset.card_insert_of_notMem (by simp [vz]),Finset.card_singleton]
    · apply independent_insert G sym irr
      · apply independent_insert G sym irr (independent_single G irr z)
        simpa using nvz
      · intro a ha
        simp only [Finset.mem_insert,Finset.mem_singleton] at ha
        rcases ha with rfl|rfl
        · exact nuv
        · exact nuz
  have ina (u : V) (hu : u ∈ A) : u ∈ insert p (A ∪ B) :=
    Finset.mem_insert_of_mem (Finset.mem_union_left _ hu)
  have inb (u : V) (hu : u ∈ B) : u ∈ insert p (A ∪ B) :=
    Finset.mem_insert_of_mem (Finset.mem_union_right _ hu)
  have dist (u : V) (hu : u∈A) (v : V) (hv : v∈B) : u≠v :=
    fun h => Finset.disjoint_left.mp dis hu (h.symm ▸ hv)
  by_cases caseA : G a a'
  · by_cases caseB : G b b'
    · have qa : ∃ u ∈ A, ¬ G p u := by
        by_cases h : G p a
        · exact ⟨a',ha',tf p a a' h caseA⟩
        · exact ⟨a,ha,h⟩
      have qb : ∃ v ∈ B, ¬ G p v := by
        by_cases h : G p b
        · exact ⟨b',hb',tf p b b' h caseB⟩
        · exact ⟨b,hb,h⟩
      obtain ⟨u,hu,nu⟩ := qa
      obtain ⟨v,hv,nv⟩ := qb
      exact mk p u v (fun h => pa (h.symm ▸ hu)) (fun h => pb (h.symm ▸ hv))
        (dist u hu v hv) (Finset.mem_insert_self _ _) (ina u hu) (inb v hv)
        nu nv (cross u hu v hv)
    · exact mk b b' a nbb (dist a ha b hb).symm (dist a ha b' hb').symm
        (inb b hb) (inb b' hb') (ina a ha) caseB
        (fun h => cross a ha b hb (sym h)) (fun h => cross a ha b' hb' (sym h))
  · exact mk a a' b naa (dist a ha b hb) (dist a' ha' b hb)
      (ina a ha) (ina a' ha') (inb b hb) caseA (cross a ha b hb) (cross a' ha' b hb)

#print axioms independent_three_one_shared
end Erdos151H13
