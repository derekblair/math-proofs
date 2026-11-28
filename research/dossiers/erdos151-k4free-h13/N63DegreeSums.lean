import N63HostAdj
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace Erdos151N63
open scoped BigOperators

theorem list_filter_count_sum {α : Type*} (P : α → Bool) (L : List α) :
    (L.filter P).length = (L.map fun i => if P i then 1 else 0).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    cases h : P a <;> simp [h,ih,Nat.add_comm]

theorem finRange_vals (n : Nat) :
    (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem pop_sum (q m : Nat) :
    pop q m = ∑ i : Fin q, if m.testBit i.val then 1 else 0 := by
  unfold pop
  rw [← finRange_vals, List.filter_map,List.length_map, list_filter_count_sum]
  rw [← List.sum_toFinset _ (List.nodup_finRange _),List.toFinset_finRange]
  rfl

theorem leftsum_bits (d q : Nat) (f : Fin d → Fin (2^q)) (j : Nat) :
    (((List.finRange d).map fun i => (f i).val).filter (·.testBit j)).length =
      ∑ i : Fin d, if (f i).val.testBit j then 1 else 0 := by
  rw [List.filter_map,List.length_map,list_filter_count_sum,
    ← List.sum_toFinset _ (List.nodup_finRange _),List.toFinset_finRange]
  rfl

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : V→V→Prop) [DecidableRel G]

theorem sum_over_slots (w : V) (irr : ¬G w w) {d q : Nat}
    (L : Fin d ≃ {z : V // G w z}) (R : Fin q ≃ {z : V // z≠w ∧ ¬G w z})
    (f : V → Nat) :
    (∑ v : V, f v) = f w + (∑ i : Fin d, f (L i).val) + (∑ j : Fin q, f (R j).val) := by
  classical
  have h := Finset.sum_equiv (slotEquiv G w irr L R)
    (s := Finset.univ) (t := Finset.univ)
    (f := fun i => f (slotVal G w L R i)) (g := f)
    (by simp) (by intro i hi; rfl)
  rw [← h,Fintype.sum_option,Fintype.sum_sum_type]
  simp [slotVal,Nat.add_assoc]

theorem deg_over_slots (w v : V) (irr : ¬G w w) {d q : Nat}
    (L : Fin d ≃ {z : V // G w z}) (R : Fin q ≃ {z : V // z≠w ∧ ¬G w z}) :
    fullDeg G v = (if G v w then 1 else 0) +
      (∑ i : Fin d, if G v (L i).val then 1 else 0) +
      (∑ j : Fin q, if G v (R j).val then 1 else 0) := by
  have h : fullDeg G v = ∑ z : V, if G v z then 1 else 0 := by
    rw [fullDeg,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [h, sum_over_slots G w irr L R]

#print axioms pop_sum
#print axioms deg_over_slots
end Erdos151N63
