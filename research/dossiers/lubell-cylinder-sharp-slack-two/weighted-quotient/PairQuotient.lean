import PrefixBand
namespace IU.Slack
open Finset

abbrev band (A : Finset Nat) (t i : Nat) := A.filter fun x => t≤x ∧ x<t+i

theorem prefix_split (A : Finset Nat) (t i : Nat) :
    pr A (t+i) = pr A t + (band A t i).card := by
  have eq : below A (t+i) = below A t ∪ band A t i := by
    ext x
    by_cases h : x ∈ A <;> simp [below,band,h] <;> omega
  have dis : Disjoint (below A t) (band A t i) := disjoint_left.mpr (by
    intro x a b
    have aa := (mem_filter.mp a).2
    have bb := (mem_filter.mp b).2.1
    omega)
  change #(below A (t+i)) = #(below A t) + #(band A t i)
  rw [eq,card_union_of_disjoint dis]

def Compatible (A B : Finset Nat) (t s : Nat) : Prop :=
  ∃ i≤s, ((A.card-t)+(B.card-t)-s)+(t-pr A t)+(t-pr B t)+i ≤
    (band A t i).card+(band B t i).card

theorem compatible_iff_witness {A B : Finset Nat} {t s : Nat}
    (aa : t≤A.card) (bb : t≤B.card) :
    Compatible A B t s ↔ ∃ i≤s,
      max t (A.card+B.card-(t+s))+(t+i) ≤ pr A (t+i)+pr B (t+i) := by
  have a := prefix_le_index A t
  have b := prefix_le_index B t
  simp only [Compatible,prefix_split]
  constructor <;> rintro ⟨i,hi,h⟩ <;> exact ⟨i,hi,by omega⟩

theorem enough_overlap (A B : Finset Nat) (i : Nat) :
    pr A i + pr B i ≤ i+(A∩B).card := by
  have u : below A i ∪ below B i ⊆ range i := by
    intro x xh
    rcases mem_union.mp xh with xh|xh <;> exact mem_range.mpr (mem_filter.mp xh).2
  have j : below A i ∩ below B i ⊆ A∩B := by
    intro x xh
    obtain ⟨h1,h2⟩ := mem_inter.mp xh
    exact mem_inter.mpr ⟨(mem_filter.mp h1).1,(mem_filter.mp h2).1⟩
  have e := card_union_add_card_inter (below A i) (below B i)
  have hu := card_le_card u
  have hj := card_le_card j
  rw [card_range] at hu
  change #(below A i) + #(below B i) ≤ _
  omega

theorem compatible_sound {A B : Finset Nat} {t s : Nat}
    (aa : t≤A.card) (bb : t≤B.card) (h : Compatible A B t s) :
    t≤(A∩B).card ∧ (A∪B).card≤t+s := by
  obtain ⟨i,_,hi⟩ := (compatible_iff_witness aa bb).mp h
  have w := enough_overlap A B (t+i)
  have c := card_union_add_card_inter A B
  omega

theorem deficit_cap {A : Finset Nat} {t s : Nat} (h : Compatible A A t s) :
    2*(t-pr A t)≤s := by
  obtain ⟨i,hi,H⟩ := h
  have sub : band A t i ⊆ (range (t+i)) \ range t := by
    intro x hx
    have j := (mem_filter.mp hx).2
    exact mem_sdiff.mpr ⟨mem_range.mpr j.2,fun z => (Nat.not_lt_of_ge j.1) (mem_range.mp z)⟩
  have cap := card_le_card sub
  rw [card_sdiff_of_subset (range_mono (by omega)),card_range,card_range] at cap
  omega

#print axioms compatible_sound
#print axioms deficit_cap
end IU.Slack
