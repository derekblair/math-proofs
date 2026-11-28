import UnblockingPools
import RamseySmall
import Mathlib.Data.Finset.Card

namespace Erdős151
open Finset

variable {V : Type*} [DecidableEq V]
variable {G : V → V → Prop}

theorem unblocked_stage_ten
    (sym : ∀ {a b}, G a b → G b a) (hcap : FreeCap G 10)
    (S E : Finset V) (dis : Disjoint S E) (hS : Free (Forbidden G) S)
    (hadd : ∀ x ∈ E, Free (Forbidden G) (insert x ↑S))
    (hs : S.card = 10) : E.card = 0 := by
  by_contra hc
  obtain ⟨x,hx⟩ := card_pos.mp (show 0 < E.card by omega)
  have h := independent_extensions_count sym hcap S {x}
    (disjoint_left.mpr (by
      intro a ha hb
      have he : a=x := mem_singleton.mp hb
      subst a
      exact disjoint_left.mp dis ha hx))
    hS (by simp [Independence]) (by simpa using hadd x hx)
  simp only [card_singleton] at h
  omega

theorem unblocked_stage_nine
    (sym : ∀ {a b}, G a b → G b a) (hcap : FreeCap G 10)
    (hlink : TriangleFreeLinks G)
    (S E : Finset V) (dis : Disjoint S E) (hS : Free (Forbidden G) S)
    (hadd : ∀ x ∈ E, Free (Forbidden G) (insert x ↑S))
    (hs : S.card = 9) : E.card ≤ 3 := by
  classical
  have clique : ∀ x ∈ E, ∀ y ∈ E, x ≠ y → G x y := by
    intro x hx y hy hne
    by_contra hn
    have hsub : ({x,y} : Finset V) ⊆ E := insert_subset_iff.mpr ⟨hx, singleton_subset_iff.mpr hy⟩
    have hi : Independence G ({x,y} : Finset V) := by
      intro a ha b hb hab
      simp only [mem_insert, mem_singleton] at ha hb
      rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
      · exact (hab rfl).elim
      · exact hn
      · exact fun hg => hn (sym hg)
      · exact (hab rfl).elim
    have h := independent_extensions_count sym hcap S {x,y}
      (disjoint_left.mpr (fun a ha hb => disjoint_left.mp dis ha (hsub hb)))
      hS hi (fun a ha => hadd a (hsub ha))
    simp [hne, hs] at h
  by_contra hh
  obtain ⟨w,hw⟩ := card_pos.mp (show 0 < E.card by omega)
  have hwc := card_erase_of_mem hw
  obtain ⟨a,ha⟩ := card_pos.mp (show 0 < (E.erase w).card by omega)
  have hac := card_erase_of_mem ha
  obtain ⟨b,hb⟩ := card_pos.mp (show 0 < ((E.erase w).erase a).card by omega)
  have hbc := card_erase_of_mem hb
  obtain ⟨c,hc⟩ := card_pos.mp (show 0 < (((E.erase w).erase a).erase b).card by omega)
  rw [mem_erase] at ha
  rw [mem_erase, mem_erase] at hb
  rw [mem_erase, mem_erase, mem_erase] at hc
  exact hlink w a b c (clique w hw a ha.2 ha.1.symm)
    (clique w hw b hb.2.2 hb.2.1.symm) (clique w hw c hc.2.2.2 hc.2.2.1.symm)
    (clique a ha.2 b hb.2.2 hb.1.symm) (clique b hb.2.2 c hc.2.2.2 hc.1.symm)
    (clique a ha.2 c hc.2.2.2 hc.2.1.symm)

/-- The weaker R(3,4)≤10 bound already suffices for the incidence contradiction. -/
theorem unblocked_stage_eight [Fintype V]
    (sym : ∀ {a b}, G a b → G b a) (hcap : FreeCap G 10)
    (hlink : TriangleFreeLinks G)
    (S E : Finset V) (dis : Disjoint S E) (hS : Free (Forbidden G) S)
    (hadd : ∀ x ∈ E, Free (Forbidden G) (insert x ↑S))
    (hs : S.card = 8) : E.card ≤ 9 := by
  classical
  let H : V → V → Prop := fun a b => a ≠ b ∧ ¬ G a b
  have hsH : ∀ {a b}, H a b → H b a := fun h => ⟨h.1.symm, fun hn => h.2 (sym hn)⟩
  have hiH : ∀ a, ¬ H a a := fun a h => h.1 rfl
  let J : V → V → Prop := fun a b => H a b ∧ a ∈ E ∧ b ∈ E
  have hsJ : ∀ {a b}, J a b → J b a := fun h => ⟨hsH h.1,h.2.2,h.2.1⟩
  have hiJ : ∀ a, ¬ J a a := fun a h => hiH a h.1
  have tfJ : Erdos151Ramsey.TriangleFree J := by
    intro a b c hab hbc hac
    have T : ({a,b,c} : Finset V) ⊆ E := by
      exact insert_subset_iff.mpr ⟨hab.2.1, insert_subset_iff.mpr ⟨hbc.2.1, singleton_subset_iff.mpr hac.2.2⟩⟩
    have hind : Independence G ({a,b,c} : Finset V) := by
      intro x hx y hy hxy
      simp only [mem_insert, mem_singleton] at hx hy
      rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl
      all_goals first | exact (hxy rfl).elim | exact hab.1.2 | exact hbc.1.2 | exact hac.1.2 |
        exact fun h => hab.1.2 (sym h) | exact fun h => hbc.1.2 (sym h) |
        exact fun h => hac.1.2 (sym h)
    have hc : ({a,b,c} : Finset V).card = 3 := by
      rw [card_insert_of_notMem (by simp [hab.1.1, hac.1.1]),
        card_insert_of_notMem (by simpa using hbc.1.1), card_singleton]
    have hx := independent_extensions_count sym hcap S {a,b,c}
      (disjoint_left.mpr (fun x hx hy => disjoint_left.mp dis hx (T hy)))
      hS hind (fun x hx => hadd x (T hx))
    omega
  by_contra! hbig
  obtain ⟨T,hTE,hT,hi⟩ := Erdos151Ramsey.independent_four_of_ten J hsJ hiJ tfJ E (by omega)
  have clique : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → G x y := by
    intro x hx y hy hn
    by_contra hg
    exact hi x hx y hy ⟨⟨hn,hg⟩,hTE hx,hTE hy⟩
  obtain ⟨w,hw⟩ := card_pos.mp (show 0 < T.card by omega)
  have hwc := card_erase_of_mem hw
  obtain ⟨a,ha⟩ := card_pos.mp (show 0 < (T.erase w).card by omega)
  have hac := card_erase_of_mem ha
  obtain ⟨b,hb⟩ := card_pos.mp (show 0 < ((T.erase w).erase a).card by omega)
  have hbc := card_erase_of_mem hb
  obtain ⟨c,hc⟩ := card_pos.mp (show 0 < (((T.erase w).erase a).erase b).card by omega)
  rw [mem_erase] at ha
  rw [mem_erase, mem_erase] at hb
  rw [mem_erase, mem_erase, mem_erase] at hc
  exact hlink w a b c (clique w hw a ha.2 ha.1.symm)
    (clique w hw b hb.2.2 hb.2.1.symm) (clique w hw c hc.2.2.2 hc.2.2.1.symm)
    (clique a ha.2 b hb.2.2 hb.1.symm) (clique b hb.2.2 c hc.2.2.2 hc.1.symm)
    (clique a ha.2 c hc.2.2.2 hc.2.1.symm)

#print axioms unblocked_stage_ten
#print axioms unblocked_stage_nine
#print axioms unblocked_stage_eight
end Erdős151
