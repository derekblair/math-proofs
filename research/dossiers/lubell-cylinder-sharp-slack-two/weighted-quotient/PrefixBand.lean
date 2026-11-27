import FamilyPrefix
namespace IU.Slack
open Finset

lemma prefix_le_index (A : Finset Nat) (i : Nat) : pr A i ≤ i := by
  have h : below A i ⊆ range i := fun a ax => mem_range.mpr (mem_filter.mp ax).2
  simpa using card_le_card h

lemma prefix_le_card (A : Finset Nat) (i : Nat) : pr A i ≤ A.card :=
  card_filter_le _ _

theorem witness_band {A B : Finset Nat} {t u s i : Nat}
    (a : A.card ≤ t+s) (b : B.card ≤ t+s)
    (h : max t (A.card+B.card-(t+u+s-u))+i ≤ pr A i+pr B i) :
    t ≤ i ∧ i ≤ t+s := by
  have hi := prefix_le_index A i
  have hj := prefix_le_index B i
  have ha := prefix_le_card A i
  have hb := prefix_le_card B i
  omega

theorem shifted_witness_band {F : Finset (Finset Nat)} {t u s : Nat}
    (ht : 0<t) (h : IsIU F (t+u+s) t u) (left : ClosedUnderPrefix F (t+u+s))
    {A B : Finset Nat} (ha : A∈F) (hb : B∈F) :
    ∃ j≤s, max t (A.card+B.card-(t+s))+(t+j) ≤ pr A (t+j)+pr B (t+j) := by
  obtain ⟨i,_,hi⟩ := prefix_compatible ht h left ha hb
  have a : A.card≤t+s := by have H := (h.2 A ha A ha).2; simpa [union_idempotent, show t+u+s-u=t+s by omega] using H
  have b : B.card≤t+s := by have H := (h.2 B hb B hb).2; simpa [union_idempotent, show t+u+s-u=t+s by omega] using H
  obtain ⟨lo,up⟩ := witness_band a b hi
  refine ⟨i-t,by omega,?_⟩
  simpa only [show t+(i-t)=i by omega,show t+u+s-u=t+s by omega] using hi

/-- The only arguments needed by the compatibility predicate are the two
profile deficits, the total sizes relative to the lower bound, and the
ranks inside the middle band, independent of the outer block lengths. -/
theorem normalize_witness {t s a b i r q pa pb : Nat}
    (lar : r≤t) (lbq : q≤t) :
    max t ((t+a)+(t+b)-(t+s))+(t+i) ≤ ((t-r)+pa)+((t-q)+pb) ↔
      (a+b-s)+r+q+i ≤ pa+pb := by omega

#print axioms shifted_witness_band
#print axioms normalize_witness
end IU.Slack
