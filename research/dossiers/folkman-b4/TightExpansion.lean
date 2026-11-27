import TightOrient
import RegularHall

namespace FolkmanB4.Tight
open Finset
variable {L V : Type*} [Fintype L] [Fintype V] [DecidableEq L] [DecidableEq V]
def shore (s : Finset L) (t : Finset V) : Nat := s.card+t.card

def NoSmallCut (I : L → V → Prop) : Prop :=
  ∀ s : Finset L, ∀ t : Finset V,
    2 ≤ shore s t → shore s t + 2 ≤ Fintype.card L + Fintype.card V →
    ¬Tight I (fun l => decide (l∈s)) (fun v => decide (v∈t))

theorem one_extra_tight (I : L → V → Prop) (s : Finset L) (t : Finset V)
    (adj : ∀ l v, I l v → v∈t → l∈s) (sz : s.card=t.card+1) :
    Tight I (fun l => decide (l∈s)) (fun v => decide (v∈t)) := by
  classical
  intro m hm
  have incl : t.image m ⊆ s := by
    intro l hl
    obtain ⟨v,hv,e⟩ := mem_image.mp hl
    exact e ▸ adj (m v) v (hm v) hv
  have one : (s \ t.image m).card=1 := by
    rw [card_sdiff_of_subset incl,card_image_of_injective _ m.injective,sz]
    omega
  obtain ⟨l,hl⟩ := card_eq_one.mp one
  have hit (v : V) : (decide (m v∈s) ≠ decide (v∈t)) ↔ m v∈s \ t.image m := by
    have E : m v∈t.image m ↔ v∈t := by
      simp [mem_image,m.injective.eq_iff]
    have hi := adj (m v) v (hm v)
    by_cases h : v∈t <;> simp [mem_sdiff,E,h,hi]
  refine ⟨m.symm l,(hit _).mpr (by simp [hl]),?_⟩
  intro v hv
  have H := (hit v).mp hv
  rw [hl,mem_singleton] at H
  exact m.apply_eq_iff_eq_symm_apply.mp H

/-- The extra-two form of Hall follows by ruling out explicit tight shores,
including the often omitted equality case. -/
theorem robust_hall (I : L → V → Prop) [DecidableRel I] (H : NoSmallCut I)
    (M : ∃ m : V ≃ L, ∀ v, I (m v) v) (t : Finset V)
    (h0 : 0<t.card) (h2 : t.card+2≤Fintype.card V) :
    t.card+2≤(t.biUnion (rows I)).card := by
  classical
  obtain ⟨m,hm⟩ := M
  let s := t.biUnion (rows I)
  change t.card+2≤s.card
  have total : Fintype.card L=Fintype.card V := (Fintype.card_congr m).symm
  have adj (l v) (e : I l v) (hv : v∈t) : l∈s :=
    mem_biUnion.mpr ⟨v,hv,mem_filter.mpr ⟨mem_univ _,e⟩⟩
  have incl : t.image m ⊆ s := by
    intro l hl
    obtain ⟨v,hv,e⟩ := mem_image.mp hl
    exact e ▸ adj (m v) v (hm v) hv
  have le := card_le_card incl
  rw [card_image_of_injective _ m.injective] at le
  by_contra no
  by_cases eq : s.card=t.card+1
  · exact H s t (by unfold shore; omega) (by unfold shore; omega)
      (one_extra_tight I s t adj eq)
  · have eq' : s.card=t.card := by omega
    have cardlt : s.card < (univ : Finset L).card := by rw [card_univ,total]; omega
    obtain ⟨l,hl⟩ := sdiff_nonempty_of_card_lt_card cardlt
    have nl := (mem_sdiff.mp hl).2
    have ins : (insert l s).card=t.card+1 := by rw [card_insert_of_notMem nl,eq']
    exact H (insert l s) t (by unfold shore; omega) (by unfold shore; omega)
      (one_extra_tight I _ t (fun a v e hv => mem_insert_of_mem (adj a v e hv)) ins)

#print axioms robust_hall
end FolkmanB4.Tight
