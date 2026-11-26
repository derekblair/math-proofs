import Mathlib.Tactic
open scoped BigOperators
namespace Interval3SUM

/-- Comparing two lexicographic targets counts all real ties, not merely a
single representative. The abstract characterization is expressed by cuts. -/
theorem count_difference {P : Type*} (S L U : Finset P) [DecidableEq P]
    (lower : L ⊆ U) (partition : S = U \ L) :
    S.card = U.card - L.card := by
  rw [partition, Finset.card_sdiff_of_subset lower]

/-- A cut crosses at most a staircase of rectangular block positions.
If a position is strictly northeast of another, the disjoint block
value ranges forbid both. The diagonal difference is therefore injective. -/
theorem cross_count {a b : ℕ} (s : Finset (Fin a × Fin b)) (ha : 0<a) (hb : 0<b)
    (cross : ∀ p∈s, ∀ q∈s, ¬(p.1.val<q.1.val ∧ p.2.val<q.2.val)) :
    s.card ≤ a+b-1 := by
  let f (p : Fin a × Fin b) : ℕ := p.1.val+(b-1-p.2.val)
  have h_inj : Set.InjOn f ↑s := by
    intro p hp q hq he
    rcases p with ⟨i,j⟩
    rcases q with ⟨k,l⟩
    change i.val+(b-1-j.val) = k.val+(b-1-l.val) at he
    have J := j.isLt; have L := l.isLt
    have hi : i.val=k.val := by
      by_contra hn
      rcases lt_or_gt_of_ne hn with lt|gt
      · exact cross (i,j) hp (k,l) hq ⟨lt,by change j.val < l.val; omega⟩
      · exact cross (k,l) hq (i,j) hp ⟨gt,by change l.val < j.val; omega⟩
    have hj : j.val=l.val := by omega
    exact Prod.ext (Fin.ext hi) (Fin.ext hj)
  have hp : s.image f ⊆ Finset.range (a+b-1) := by
    intro k hk
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hk
    apply Finset.mem_range.mpr
    have h := v.1.isLt
    change v.1.val+(b-1-v.2.val)<a+b-1
    omega
  have h := Finset.card_le_card hp
  rw [Finset.card_image_of_injOn h_inj,Finset.card_range] at h
  exact h

end Interval3SUM
#print axioms Interval3SUM.count_difference
#print axioms Interval3SUM.cross_count
