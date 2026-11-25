import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Card

namespace PermCircles

def badLow {n m : ℕ} (p : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (p i).val < m)

def badHigh {n m : ℕ} (p : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => n-1-(p i).val < m)

lemma badLow_card {n m : ℕ} (p : Equiv.Perm (Fin n)) :
    (badLow (m:=m) p).card ≤ m := by
  let e : (badLow (m:=m) p : Type) → Fin m := fun ⟨i,hi⟩ => ⟨(p i).val, (Finset.mem_filter.mp hi).2⟩
  have he : Function.Injective e := by
    intro i j h
    apply Subtype.ext
    apply p.injective
    apply Fin.ext
    have h' := congrArg (fun k : Fin m => k.val) h
    exact h'
  simpa using Fintype.card_le_of_injective e he

lemma badHigh_card {n m : ℕ} (p : Equiv.Perm (Fin n)) :
    (badHigh (m:=m) p).card ≤ m := by
  let e : (badHigh (m:=m) p : Type) → Fin m := fun ⟨i,hi⟩ =>
    ⟨n-1-(p i).val, (Finset.mem_filter.mp hi).2⟩
  have he : Function.Injective e := by
    intro i j h
    apply Subtype.ext
    apply p.injective
    apply Fin.ext
    have hi := (p i.val).isLt
    have hj := (p j.val).isLt
    have hh := congrArg Fin.val h
    change n-1-(p i.val).val = n-1-(p j.val).val at hh
    omega
  simpa using Fintype.card_le_of_injective e he

def bad {n : ℕ} (m : ℕ) (p : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  (badLow (m:=m) (.refl _) ∪ badHigh (m:=m) (.refl _)) ∪
  (badLow (m:=m) p ∪ badHigh (m:=m) p)

def good {n : ℕ} (m : ℕ) (p : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ \ bad m p

lemma card_good {n m : ℕ} (p : Equiv.Perm (Fin n)) :
    n ≤ (good m p).card+4*m := by
  have h1 := Finset.card_union_le (badLow (m:=m) (Equiv.refl (Fin n))) (badHigh (m:=m) (.refl _))
  have h2 := Finset.card_union_le (badLow (m:=m) p) (badHigh (m:=m) p)
  have h3 := Finset.card_union_le
    (badLow (m:=m) (.refl (Fin n)) ∪ badHigh (m:=m) (.refl _))
    (badLow (m:=m) p ∪ badHigh (m:=m) p)
  have h4 : (bad m p).card ≤ 4*m := by
    unfold bad
    have l1 := badLow_card (m:=m) (Equiv.refl (Fin n))
    have l2 := badHigh_card (m:=m) (Equiv.refl (Fin n))
    have l3 := badLow_card (m:=m) p
    have l4 := badHigh_card (m:=m) p
    omega
  have he : (good m p).card + (bad m p).card = n := by
    unfold good
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)]
    simp
  omega

lemma good_bounds {n m : ℕ} {p : Equiv.Perm (Fin n)} {i : Fin n} (h : i ∈ good m p) :
    m ≤ i.val ∧ m ≤ (p i).val ∧ m ≤ n-1-i.val ∧ m ≤ n-1-(p i).val := by
  have hn : i ∉ bad m p := (Finset.mem_sdiff.mp h).2
  unfold bad at hn
  have hL : i ∉ badLow (m:=m) (Equiv.refl (Fin n)) := fun hi =>
    hn (Finset.mem_union_left _ (Finset.mem_union_left _ hi))
  have hH : i ∉ badHigh (m:=m) (Equiv.refl (Fin n)) := fun hi =>
    hn (Finset.mem_union_left _ (Finset.mem_union_right _ hi))
  have hLp : i ∉ badLow (m:=m) p := fun hi =>
    hn (Finset.mem_union_right _ (Finset.mem_union_left _ hi))
  have hHp : i ∉ badHigh (m:=m) p := fun hi =>
    hn (Finset.mem_union_right _ (Finset.mem_union_right _ hi))
  constructor
  · exact Nat.le_of_not_gt (fun hi => hL (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩))
  constructor
  · exact Nat.le_of_not_gt (fun hi => hLp (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩))
  constructor
  · exact Nat.le_of_not_gt (fun hi => hH (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩))
  · exact Nat.le_of_not_gt (fun hi => hHp (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩))

#print axioms card_good
#print axioms good_bounds
end PermCircles
