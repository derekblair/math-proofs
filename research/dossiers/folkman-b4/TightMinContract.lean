import TightMinimum

namespace FolkmanB4.Tight
open Finset
variable {L V : Type*} [Fintype L] [Fintype V] [DecidableEq L] [DecidableEq V]

theorem minimal_contraction_no_cut (I : L → V → Prop) (S : Finset L) (T : Finset V)
    (large : Nontrivial S T)
    (inward : Inward I (fun l => decide (l∈S)) (fun v => decide (v∈T)))
    (tight : Tight I (fun l => decide (l∈S)) (fun v => decide (v∈T)))
    (mini : ∀ a b, Nontrivial a b →
        Tight I (fun l => decide (l∈a)) (fun v => decide (v∈b)) →
        shore S T ≤ shore a b) :
    NoSmallCut (pointsContraction I (fun l => decide (l∈S)) (fun v => decide (v∈T))) := by
  let A (l : L) : Bool := decide (l∈S)
  let B (v : V) : Bool := decide (v∈T)
  let Q := pointsContraction I A B
  suffices aux : ∀ (s : Finset (In A)) (t : Finset (Option (In B))),
      Nontrivial s t → none∉t →
      ¬ Tight Q (fun l => decide (l∈s)) (fun v => decide (v∈t)) by
    intro s t h1 h2 ht
    by_cases hn : none∈t
    · have sc := card_compl s
      have tc := card_compl t
      change 2 ≤ shore s t at h1
      change shore s t + 2 ≤ Fintype.card (In A) + Fintype.card (Option (In B)) at h2
      have cc : s.card ≤ Fintype.card (In A) := card_le_univ s
      have dd : t.card ≤ Fintype.card (Option (In B)) := card_le_univ t
      change _ = Fintype.card (In A) - s.card at sc
      change _ = Fintype.card (Option (In B)) - t.card at tc
      have ker : 2 ≤ sᶜ.card + tᶜ.card ∧ sᶜ.card + tᶜ.card + 2 ≤
          Fintype.card (In A) + Fintype.card (Option (In B)) := by
        unfold shore at h1 h2
        omega
      exact aux sᶜ tᶜ ker
        (by simpa using hn) (complement_tight s t ht)
    · exact aux s t ⟨h1,h2⟩ hn ht
  intro s t st out small
  let a := s.image Subtype.val
  let b := (t.preimage some (by intro v _ w _ h; exact Option.some.inj h)).image Subtype.val
  have ca : a.card=s.card := card_image_of_injective _ Subtype.val_injective
  have cb : b.card=t.card := by
    unfold b
    rw [card_image_of_injective _ Subtype.val_injective]
    have e : (t.preimage some (by intro v _ w _ h; exact Option.some.inj h)).image some=t := by
      ext v
      cases v with
      | none => simp [out]
      | some v => simp [mem_image]; exact Finset.mem_preimage
    conv_rhs => rw [← e]
    exact (card_image_of_injective _ (Option.some_injective _)).symm
  have eqL (l : L) : restrictBool A (fun z => decide (z∈s)) l = decide (l∈a) := by
    unfold restrictBool
    split
    · rename_i h
      have iff : l∈a ↔ (⟨l,h⟩ : In A)∈s := by
        simp only [a,mem_image,Subtype.exists]
        constructor
        · rintro ⟨w,hw,W,rfl⟩
          exact W
        · intro W
          exact ⟨l,h,W,rfl⟩
      simp [iff]
    · rename_i h
      have n : l∉a := by
        intro x
        obtain ⟨u,_,rfl⟩ := mem_image.mp x
        exact h u.property
      simp [n]
  have eqV (v : V) :
      restrictBool B ((fun z => decide (z∈t)) ∘ some) v = decide (v∈b) := by
    unfold restrictBool
    split
    · rename_i h
      have iff : v∈b ↔ some (⟨v,h⟩ : In B)∈t := by
        change v∈b ↔ _
        simp only [b,mem_image,Subtype.exists]
        constructor
        · rintro ⟨w,hw,W,rfl⟩
          exact Finset.mem_preimage.mp W
        · intro W
          exact ⟨v,h,Finset.mem_preimage.mpr W,rfl⟩
      simp [iff]
    · rename_i h
      have n : v∉b := by
        intro x
        obtain ⟨u,_,rfl⟩ := mem_image.mp x
        exact h u.property
      simp [n]
  have lifted := quotient_cut_lifts I A B inward tight
    (fun l => decide (l∈s)) (fun v => decide (v∈t)) (by simp [out]) small
  rw [funext eqL,funext eqV] at lifted
  have szA : Fintype.card (In A)=S.card := card_inside S
  have szB : Fintype.card (Option (In B))=T.card+1 := by
    rw [Fintype.card_option, show Fintype.card (In B)=T.card from card_inside T]
  have ⟨ha,hb⟩ := st
  have ⟨_,hl⟩ := large
  unfold shore at *
  rw [szA,szB] at hb
  have smallne : Nontrivial a b := by
    unfold Nontrivial shore
    omega
  have contrary := mini a b smallne lifted
  unfold shore at contrary
  omega

#print axioms minimal_contraction_no_cut
end FolkmanB4.Tight
