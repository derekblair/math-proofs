import CriticalPfaffian

namespace FolkmanB4.Critical
open Finset

/-- A finite minimally non-bicolourable, subcubic triple system has a cubic
incidence matrix, and all its supported perfect matchings have one parity. -/
theorem cubic_and_same_parity {L V : Type*} [Fintype L] [Fintype V] [DecidableEq V]
    (I : L → V → Prop) [DecidableRel I] (used : ∀ v, ∃ l, I l v)
    (bad : ¬∃ c, Good I univ c)
    (minimal : ∀ S : Finset L, S≠univ → ∃ c, Good I S c)
    (row : ∀ l, pts I l=3) (col : ∀ v, lns I v≤3) :
    (∀ v, lns I v=3) ∧
      ∃ e : V ≃ L, ∀ s t : V ≃ L, (∀ i, I (s i) i) → (∀ i, I (t i) i) →
        pSign (s.trans e.symm) = pSign (t.trans e.symm) := by
  classical
  obtain ⟨E,hc⟩ := cubic I used bad minimal row col
  let e : V ≃ L := Fintype.equivOfCardEq E
  let J (a b : V) := I (e a) b
  have ju (v : V) : ∃ a, J a v := by
    obtain ⟨l,h⟩ := used v
    exact ⟨e.symm l,by simpa [J] using h⟩
  have jb : ¬ ∃ c, Good J univ c := by
    rintro ⟨c,h⟩
    apply bad
    refine ⟨c,fun l _ => ?_⟩
    have H := h (e.symm l) (mem_univ _)
    simpa [J] using H
  have jm (S : Finset V) (hne : S≠univ) : ∃ c, Good J S c := by
    let T := S.image e
    have n : T≠univ := by
      intro H
      apply hne
      apply eq_univ_of_forall
      intro v
      have mv : e v∈T := by rw [H]; exact mem_univ _
      obtain ⟨w,ws,we⟩ := mem_image.mp mv
      rwa [e.injective we] at ws
    obtain ⟨c,h⟩ := minimal T n
    exact ⟨c,fun v hv => h _ (mem_image_of_mem _ hv)⟩
  refine ⟨hc,e,fun s t hs ht => ?_⟩
  let _ : DecidableRel J := fun u v => inferInstanceAs (Decidable (I (e u) v))
  have hs' : supported J (s.trans e.symm) := fun i => by simpa [J] using hs i
  have ht' : supported J (t.trans e.symm) := fun i => by simpa [J] using ht i
  exact square_has_constant_sign J ju jb jm hs' ht'

#print axioms cubic_and_same_parity
end FolkmanB4.Critical
