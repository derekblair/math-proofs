import N63ArithmeticCode
import Init.Data.Nat.Bitwise.Lemmas

namespace Erdos151N63

theorem and_zero_of_no_overlap {a b q : Nat} (ha : a < 2^q)
    (h : ∀ j < q, a.testBit j = true → b.testBit j = false) :
    a &&& b = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and]
  by_cases hj : j < q
  · by_cases ha' : a.testBit j = true
    · simp [ha',h j hj ha']
    · have he : a.testBit j = false := Bool.eq_false_of_not_eq_true ha'
      simp [he]
  · have he : a.testBit j = false := Nat.testBit_lt_two_pow
      (ha.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [he]

theorem mem_pairs_iff (q a b : Nat) :
    (a,b) ∈ pairs q ↔ a < q ∧ b < q ∧ a < b := by
  unfold pairs
  simp only [List.mem_flatMap,List.mem_map,List.mem_filter,List.mem_range,
    decide_eq_true_eq,Prod.mk.injEq]
  constructor
  · rintro ⟨u,hu,v,⟨hv,huv⟩,rfl,rfl⟩
    exact ⟨hu,hv,huv⟩
  · rintro ⟨ha,hb,hab⟩
    exact ⟨a,ha,b,⟨hb,hab⟩,rfl,rfl⟩

theorem tfRight_of_bits (q : Nat) (H : Array Nat)
    (width : ∀ i < q, mask H i < 2^q)
    (tf : ∀ a b j, a < q → b < q → j < q → adj H a b = true →
      adj H a j = true → adj H b j = false) :
    tfRight q H = true := by
  unfold tfRight
  rw [List.all_eq_true]
  rintro ⟨a,b⟩ h
  obtain ⟨ha,hb,_⟩ := (mem_pairs_iff q a b).mp h
  cases e : adj H a b
  · simp [e]
  · have hz : mask H a &&& mask H b = 0 :=
      and_zero_of_no_overlap (width a ha) (tf a b · ha hb · e)
    simp [e,hz]

theorem allowed_of_bits (q : Nat) (H : Array Nat) (m : Fin (2^q))
    (width : ∀ i < q, mask H i < 2^q)
    (indep : ∀ j k, j < q → k < q → m.val.testBit j = true →
      adj H j k = true → m.val.testBit k = false) :
    allowed q H m = true := by
  unfold allowed
  rw [List.all_eq_true]
  intro j hj
  have hj' := List.mem_range.mp hj
  cases e : m.val.testBit j
  · simp [e]
  · have hz : mask H j &&& m.val = 0 :=
      and_zero_of_no_overlap (width j hj') (indep j · hj' · e)
    simp [e,hz]

#print axioms tfRight_of_bits
#print axioms allowed_of_bits
end Erdos151N63
