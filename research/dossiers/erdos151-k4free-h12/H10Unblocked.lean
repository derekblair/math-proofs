import UnblockingPools
import RamseySmall
import Mathlib.Data.Finset.Card

namespace Erdős151.H10
open Finset

variable {V : Type*} [DecidableEq V]
variable {G : V → V → Prop}

theorem unblocked_stage_nine
    (sym : ∀ {a b}, G a b → G b a) (hcap : FreeCap G 9)
    (S E : Finset V) (dis : Disjoint S E) (hS : Free (Forbidden G) S)
    (hadd : ∀ x ∈ E, Free (Forbidden G) (insert x ↑S))
    (hs : S.card = 9) : E.card = 0 := by
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

theorem unblocked_stage_eight
    (sym : ∀ {a b}, G a b → G b a) (hcap : FreeCap G 9)
    (hlink : TriangleFreeLinks G)
    (S E : Finset V) (dis : Disjoint S E) (hS : Free (Forbidden G) S)
    (hadd : ∀ x ∈ E, Free (Forbidden G) (insert x ↑S))
    (hs : S.card = 8) : E.card ≤ 3 := by
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


#print axioms unblocked_stage_nine
#print axioms unblocked_stage_eight
end Erdős151.H10
