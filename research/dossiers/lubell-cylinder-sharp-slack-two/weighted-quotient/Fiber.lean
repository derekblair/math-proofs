import Saturated
import Mathlib.Data.Finset.Prod
namespace IU.Slack
open Finset

abbrev tail (A : Bag) (t s : Nat) := A.filter (fun x => t+s≤x)
abbrev mid (t s : Nat) := range (t+s) \ range t
abbrev last (n t s : Nat) := range n \ range (t+s)

def fiber (n t s a z : Nat) (M : Bag) : Sys :=
  (((range t).powersetCard a) ×ˢ ((last n t s).powersetCard z)).image
    (fun P => P.1 ∪ M ∪ P.2)

theorem split_parts (A : Bag) (t s : Nat) :
    below A t ∪ band A t s ∪ tail A t s = A := by
  ext x
  by_cases h : x ∈ A <;> simp [below,band,tail,h] <;> omega

theorem read_left {L M R : Bag} {n t s : Nat}
    (l : L⊆range t) (m : M⊆mid t s) (r : R⊆last n t s) :
    below (L∪M∪R) t = L := by
  ext x
  constructor
  · intro h
    obtain ⟨hh,hx⟩ := mem_filter.mp h
    rcases mem_union.mp hh with h|h
    · rcases mem_union.mp h with h|h
      · exact h
      · exact False.elim ((mem_sdiff.mp (m h)).2 (mem_range.mpr hx))
    · have hp : t+s≤x := Nat.le_of_not_gt fun e => (mem_sdiff.mp (r h)).2 (mem_range.mpr e)
      omega
  · intro h
    exact mem_filter.mpr ⟨mem_union.mpr (Or.inl (mem_union.mpr (Or.inl h))),mem_range.mp (l h)⟩

theorem read_middle {L M R : Bag} {n t s : Nat}
    (l : L⊆range t) (m : M⊆mid t s) (r : R⊆last n t s) :
    band (L∪M∪R) t s = M := by
  ext x
  constructor
  · intro h
    obtain ⟨hh,hxt,hxs⟩ := mem_filter.mp h
    rcases mem_union.mp hh with h|h
    · rcases mem_union.mp h with h|h
      · exact False.elim ((Nat.not_lt_of_ge hxt) (mem_range.mp (l h)))
      · exact h
    · exact False.elim ((mem_sdiff.mp (r h)).2 (mem_range.mpr hxs))
  · intro h
    obtain ⟨h1,h2⟩ := mem_sdiff.mp (m h)
    exact mem_filter.mpr ⟨mem_union.mpr (Or.inl (mem_union.mpr (Or.inr h))),
      Nat.le_of_not_gt (fun e => h2 (mem_range.mpr e)),mem_range.mp h1⟩

theorem read_right {L M R : Bag} {n t s : Nat}
    (l : L⊆range t) (m : M⊆mid t s) (r : R⊆last n t s) :
    tail (L∪M∪R) t s = R := by
  ext x
  constructor
  · intro h
    obtain ⟨hh,hx⟩ := mem_filter.mp h
    rcases mem_union.mp hh with h|h
    · rcases mem_union.mp h with h|h
      · have z := mem_range.mp (l h)
        omega
      · exact False.elim ((Nat.not_lt_of_ge hx) (mem_range.mp (mem_sdiff.mp (m h)).1))
    · exact h
  · intro h
    exact mem_filter.mpr ⟨mem_union.mpr (Or.inr h),
      Nat.le_of_not_gt (fun e => (mem_sdiff.mp (r h)).2 (mem_range.mpr e))⟩

theorem fiber_card {n t s a z : Nat} {M : Bag} (m : M⊆mid t s) (h : t+s≤n) :
    (fiber n t s a z M).card = (t.choose a)*((n-(t+s)).choose z) := by
  classical
  unfold fiber
  rw [card_image_of_injOn,card_product,card_powersetCard,card_powersetCard,
    card_range,card_sdiff_of_subset (range_mono h),card_range,card_range]
  intro X x Y y e
  obtain ⟨x1,x2⟩ := mem_product.mp x
  obtain ⟨y1,y2⟩ := mem_product.mp y
  have l1 := (mem_powersetCard.mp x1).1
  have l2 := (mem_powersetCard.mp y1).1
  have r1 := (mem_powersetCard.mp x2).1
  have r2 := (mem_powersetCard.mp y2).1
  change X.1 ∪ M ∪ X.2 = Y.1 ∪ M ∪ Y.2 at e
  apply Prod.ext
  · rw [←read_left l1 m r1,←read_left l2 m r2,e]
  · rw [←read_right l1 m r1,←read_right l2 m r2,e]

theorem fiber_mem {A M : Bag} {n t s a z : Nat} (m : M⊆mid t s) (h : t+s≤n) :
    A∈fiber n t s a z M ↔
    A⊆range n ∧ pr A t=a ∧ band A t s=M ∧ (tail A t s).card=z := by
  classical
  unfold fiber
  constructor
  · intro ha
    obtain ⟨⟨L,R⟩,p,rfl⟩ := mem_image.mp ha
    obtain ⟨l,r⟩ := mem_product.mp p
    obtain ⟨ls,lc⟩ := mem_powersetCard.mp l
    obtain ⟨rs,rc⟩ := mem_powersetCard.mp r
    have i : t≤n := by omega
    have ms : M⊆range n := fun x hx => range_mono h (mem_sdiff.mp (m hx)).1
    have rr : R⊆range n := fun _ x => (mem_sdiff.mp (rs x)).1
    refine ⟨union_subset (union_subset (ls.trans (range_mono i)) ms) rr,?_,?_,?_⟩
    · change #(below (L∪M∪R) t)=a
      rw [read_left ls m rs,lc]
    · exact read_middle ls m rs
    · rw [read_right ls m rs,rc]
  · rintro ⟨as,al,am,ar⟩
    have ls : below A t⊆range t := fun x hx => mem_range.mpr (mem_filter.mp hx).2
    have rs : tail A t s⊆last n t s := by
      intro x hx
      obtain ⟨a,r⟩ := mem_filter.mp hx
      exact mem_sdiff.mpr ⟨as a, fun xq => (Nat.not_lt_of_ge r) (mem_range.mp xq)⟩
    refine mem_image.mpr ⟨(below A t,tail A t s),
      mem_product.mpr ⟨mem_powersetCard.mpr ⟨ls,al⟩,mem_powersetCard.mpr ⟨rs,ar⟩⟩,?_⟩
    rw [←am,split_parts]

#print axioms fiber_card
#print axioms fiber_mem
end IU.Slack
