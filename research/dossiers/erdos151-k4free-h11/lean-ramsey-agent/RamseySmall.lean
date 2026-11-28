import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Fin

namespace Erdos151Ramsey

variable {V : Type*} [Fintype V] [DecidableEq V]

def TriangleFree (G : V → V → Prop) : Prop :=
  ∀ a b c, G a b → G b c → ¬ G a c

def Independent (G : V → V → Prop) (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ¬ G a b

variable (G : V → V → Prop) [DecidableRel G]

theorem independent_near (h : TriangleFree G) (v : V) (S : Finset V) :
    Independent G (S.filter (G v)) := by
  intro a ha b hb hab
  exact h v a b (Finset.mem_filter.mp ha).2 hab (Finset.mem_filter.mp hb).2

theorem independent_insert (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) {S : Finset V} {v : V}
    (h : Independent G S) (hn : ∀ a ∈ S, ¬ G v a) :
    Independent G (insert v S) := by
  intro a ha b hb hab
  rcases Finset.mem_insert.mp (show a ∈ insert v S from ha) with rfl | haS
  · rcases Finset.mem_insert.mp hb with rfl | hb
    · exact irr _ hab
    · exact hn b hb hab
  · rcases Finset.mem_insert.mp (show b ∈ insert v S from hb) with rfl | hb
    · exact hn a haS (sym hab)
    · exact h a haS b hb hab

def far (v : V) (S : Finset V) : Finset V :=
  (S.erase v).filter (fun u => ¬ G v u)

theorem far_card (irr : ∀ a, ¬ G a a) (v : V) (S : Finset V) (hv : v ∈ S) :
    (far G v S).card + (S.filter (G v)).card + 1 = S.card := by
  have h : ((S.erase v).filter (G v)) = S.filter (G v) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · exact fun ⟨⟨_, hs⟩, ha⟩ => ⟨hs, ha⟩
    · intro ⟨hs, ha⟩
      refine ⟨⟨?_, hs⟩, ha⟩
      rintro rfl
      exact irr _ ha
  have he := Finset.card_filter_add_card_filter_not (s := S.erase v) (p := G v)
  rw [h] at he
  have her := Finset.card_erase_add_one hv
  unfold far
  omega

theorem independent_two_of_three (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) (h : TriangleFree G) (S : Finset V) (hc : 3 ≤ S.card) :
    ∃ T ⊆ S, 2 ≤ T.card ∧ Independent G T := by
  by_contra! hn
  have ha : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → G a b := by
    intro a as b bs hnab
    by_contra hab
    apply hn {a,b}
    · exact Finset.insert_subset_iff.mpr ⟨as, Finset.singleton_subset_iff.mpr bs⟩
    · rw [Finset.card_insert_of_notMem (by simpa using hnab), Finset.card_singleton]
    · apply independent_insert G sym irr
      · intro x hx y hy
        simp only [Finset.mem_singleton] at hx hy
        subst x; subst y
        exact irr _
      · simpa using hab
  obtain ⟨a, haS⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  obtain ⟨b, hbS⟩ := Finset.card_pos.mp (show 0 < (S.erase a).card by
    have := Finset.card_erase_add_one haS
    omega)
  obtain ⟨c, hcS⟩ := Finset.card_pos.mp (show 0 < ((S.erase a).erase b).card by
    have := Finset.card_erase_add_one haS
    have := Finset.card_erase_add_one hbS
    omega)
  obtain ⟨hcb, hcS⟩ := Finset.mem_erase.mp hcS
  obtain ⟨hca, hcS⟩ := Finset.mem_erase.mp hcS
  obtain ⟨hba, hbS⟩ := Finset.mem_erase.mp hbS
  exact h a b c (ha a haS b hbS hba.symm) (ha b hbS c hcS hcb.symm)
    (ha a haS c hcS hca.symm)

theorem independent_three_of_six (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) (h : TriangleFree G) (S : Finset V) (hc : 6 ≤ S.card) :
    ∃ T ⊆ S, 3 ≤ T.card ∧ Independent G T := by
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  by_cases hn : 3 ≤ (S.filter (G v)).card
  · exact ⟨_, Finset.filter_subset _ _, hn, independent_near G h v S⟩
  · have hf := far_card G irr v S hv
    obtain ⟨T, hT, hcard, hind⟩ := independent_two_of_three G sym irr h (far G v S) (by omega)
    have hfar := fun x hx => Finset.mem_filter.mp (hT (show x ∈ T from hx))
    have hnot : v ∉ T := fun hm => (Finset.mem_erase.mp (hfar v hm).1).1 rfl
    refine ⟨insert v T, ?_, ?_, independent_insert G sym irr hind (fun x hx => (hfar x hx).2)⟩
    · exact Finset.insert_subset_iff.mpr ⟨hv, fun x hx => Finset.mem_of_mem_erase (hfar x hx).1⟩
    · rw [Finset.card_insert_of_notMem hnot]; omega

theorem ramsey33 (G : Fin 6 → Fin 6 → Prop) [DecidableRel G] (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) (h : TriangleFree G) :
    ∃ T, 3 ≤ T.card ∧ Independent G T := by
  obtain ⟨T, _, hc, hi⟩ := independent_three_of_six G sym irr h Finset.univ (by simp)
  exact ⟨T, hc, hi⟩

theorem independent_four_of_ten (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (h : TriangleFree G) (S : Finset V) (hc : 10 ≤ S.card) :
    ∃ T ⊆ S, 4 ≤ T.card ∧ Independent G T := by
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  by_cases hn : 4 ≤ (S.filter (G v)).card
  · exact ⟨_, Finset.filter_subset _ _, hn, independent_near G h v S⟩
  · have hf := far_card G irr v S hv
    obtain ⟨T, hT, hcard, hind⟩ := independent_three_of_six G sym irr h (far G v S) (by omega)
    have hfar := fun x hx => Finset.mem_filter.mp (hT (show x ∈ T from hx))
    have hnot : v ∉ T := fun hm => (Finset.mem_erase.mp (hfar v hm).1).1 rfl
    refine ⟨insert v T, ?_, ?_, independent_insert G sym irr hind (fun x hx => (hfar x hx).2)⟩
    · exact Finset.insert_subset_iff.mpr ⟨hv, fun x hx => Finset.mem_of_mem_erase (hfar x hx).1⟩
    · rw [Finset.card_insert_of_notMem hnot]; omega

theorem ramsey34_le10 (G : Fin 10 → Fin 10 → Prop) [DecidableRel G] (sym : ∀ {a b}, G a b → G b a)
    (irr : ∀ a, ¬ G a a) (h : TriangleFree G) :
    ∃ T, 4 ≤ T.card ∧ Independent G T := by
  obtain ⟨T, _, hc, hi⟩ := independent_four_of_ten G sym irr h Finset.univ (by simp)
  exact ⟨T, hc, hi⟩

#print axioms ramsey33
#print axioms ramsey34_le10
end Erdos151Ramsey
