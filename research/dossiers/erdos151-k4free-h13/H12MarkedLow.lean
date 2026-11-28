import MarkedLinkTable
import Mathlib.Data.Finset.Card

namespace Erdos151H12

theorem type2_low_neighbors (u v : Fin 8) (hu : Erdos151MarkedLinkTable.deg 2 u = 2) :
    Erdos151MarkedLinkTable.adj 2 u v = true ↔ Erdos151MarkedLinkTable.deg 2 v = 4 := by
  revert u v
  decide

/-- If every nonempty low class at a vertex has two members, and each low edge makes
its endpoints share their nonempty high classes, then no low class exists as long as
the symmetric high relation has degree at most two. -/
theorem low_classes_empty {V : Type*} [DecidableEq V] (high low : V → Finset V)
    (no_loop : ∀ v, v ∉ low v)
    (low_count : ∀ v, (low v).card = 0 ∨ (low v).card = 2)
    (high_bound : ∀ v, (high v).card ≤ 2)
    (high_symm : ∀ x y, y ∈ high x → x ∈ high y)
    (high_nonempty : ∀ x y, y ∈ low x → (high x).Nonempty)
    (low_transfer : ∀ x y, y ∈ low x → high x = high y) :
    ∀ v, (low v).card = 0 := by
  intro v
  rcases low_count v with z | h
  · exact z
  · exfalso
    obtain ⟨y, hy⟩ := Finset.card_pos.mp (show 0 < (low v).card by omega)
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (show 0 < ((low v).erase y).card by
      have := Finset.card_erase_add_one hy
      omega)
    obtain ⟨hnzy, hz⟩ := Finset.mem_erase.mp hz
    have hnvy : v ≠ y := fun e => no_loop v (e ▸ hy)
    have hnvz : v ≠ z := fun e => no_loop v (e ▸ hz)
    obtain ⟨a, ha⟩ := high_nonempty v y hy
    have hay : a ∈ high y := low_transfer v y hy ▸ ha
    have haz : a ∈ high z := low_transfer v z hz ▸ ha
    have hh : ({v,y,z} : Finset V) ⊆ high a := by
      exact Finset.insert_subset_iff.mpr ⟨high_symm v a ha, Finset.insert_subset_iff.mpr
        ⟨high_symm y a hay, Finset.singleton_subset_iff.mpr (high_symm z a haz)⟩⟩
    have hc := Finset.card_le_card hh
    have hv : v ∉ ({y,z} : Finset V) := by simp [hnvy, hnvz]
    have hy' : y ∉ ({z} : Finset V) := by simpa only [Finset.mem_singleton] using hnzy.symm
    rw [Finset.card_insert_of_notMem hv, Finset.card_insert_of_notMem hy', Finset.card_singleton] at hc
    have hb := high_bound a
    omega

#print axioms type2_low_neighbors
#print axioms low_classes_empty
end Erdos151H12
