import FanoLabels

namespace FolkmanB4.Fano
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {S : Finset (Finset (Finset V))}

theorem actual_line (w : Fin 7 ↪ Finset V) (l : Fin 7) {t : Finset (Finset V)}
    (ct : t.card=3) (h : ∀ p, inc l p → w p∈t) : (line l).image w=t := by
  have ss : (line l).image w⊆t := by
    intro x hx
    obtain ⟨p,hp,e⟩ := mem_image.mp hx
    exact e ▸ h p hp
  apply eq_of_subset_of_card_le ss
  rw [card_image_of_injective _ w.injective,canonical_card,ct]

def named (S : Finset (Finset (Finset V))) (w : Fin 7 ↪ Finset V) (l : Fin 7) : Prop :=
  ∃ t∈S, t.card=3 ∧ ∀ p, inc l p → w p∈t

theorem named_mem (w : Fin 7 ↪ Finset V) {l : Fin 7} (h : named S w l) :
    (line l).image w∈S := by
  obtain ⟨t,T,c,edges⟩ := h
  rwa [actual_line w l c edges]

theorem line_fragment_of_named (w : Fin 7 ↪ Finset V) (hw : ∀ i, (w i).card=2)
    (h : ∀ l : Fin 7, l≠0 → named S w l) : HasLineFragment S := by
  refine ⟨w,hw,?_,?_,?_,?_,?_,?_⟩
  · simpa [line] using named_mem w (h 1 (by decide))
  · simpa [line] using named_mem w (h 2 (by decide))
  · simpa [line] using named_mem w (h 3 (by decide))
  · simpa [line] using named_mem w (h 4 (by decide))
  · simpa [line] using named_mem w (h 5 (by decide))
  · simpa [line] using named_mem w (h 6 (by decide))

theorem point_fragment_of_named (w : Fin 7 ↪ Finset V) (hw : ∀ i, (w i).card=2)
    (l0 : named S w 0) (l1 : named S w 1) (l3 : named S w 3)
    (l6 : named S w 6) (l2 : named S w 2) : HasPointFragment S := by
  refine ⟨w,hw,?_,?_,?_,?_,?_⟩
  · simpa [line] using named_mem w l0
  · simpa [line] using named_mem w l1
  · simpa [line] using named_mem w l3
  · simpa [line] using named_mem w l6
  · simpa [line] using named_mem w l2

#print axioms line_fragment_of_named
#print axioms point_fragment_of_named
end FolkmanB4.Fano
