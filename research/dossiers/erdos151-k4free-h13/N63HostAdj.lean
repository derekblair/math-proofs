import N63Index

namespace Erdos151N63

theorem maskList_read (d q : Nat) (f : Fin d → Fin (2^q)) (i : Fin d) :
    (((List.finRange d).map fun i => (f i).val)[i.val]?.getD 0) = (f i).val := by
  have h : i.val < ((List.finRange d).map fun i => (f i).val).length := by simpa using i.isLt
  simp [List.getElem?_eq_getElem h,Fin.eta]

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : V→V→Prop) [DecidableRel G]

/-- The constructed matrix is exactly the original graph on the
three-block coordinate index, not merely a subgraph. -/
theorem hostAdj_slots (w : V) {d q : Nat} (H : Array Nat) (f : Fin d → Fin (2^q))
    (L : Fin d ≃ {z : V // G w z}) (R : Fin q ≃ {z : V // z≠w ∧ ¬G w z})
    (sym : ∀ a b, G a b ↔ G b a) (irr : ¬G w w)
    (hL : ∀ i j, ¬G (L i).val (L j).val)
    (hM : ∀ i j : Fin q, adj H i.val j.val = decide (G (R i).val (R j).val))
    (hB : ∀ i j, (f i).val.testBit j.val = decide (G (L i).val (R j).val))
    (a b : Slot d q) :
    adj (buildRows d q H f) (indexVal a) (indexVal b) =
      decide (G (slotVal G w L R a) (slotVal G w L R b)) := by
  let ts := (List.finRange d).map (fun i => (f i).val)
  have hd : ts.length = d := by simp [ts]
  change adj (buildRaw d q H ts) _ _ = _
  rcases a with _|(i|i) <;> rcases b with _|(j|j) <;> simp only [indexVal,slotVal]
  · simp [buildAdj_pivot,irr]
  · have hj : j.val+1≤d := by omega
    simp [buildAdj_pivot,hj,(L j).property]
  · have hj : ¬d+1+j.val≤d := by omega
    simp [buildAdj_pivot,hj,(R j).property.2]
  · rw [buildAdj_left _ _ _ _ hd _ _ i.isLt]
    simp [(sym _ _).2 (L i).property]
  · rw [buildAdj_left _ _ _ _ hd _ _ i.isLt]
    have hj : ¬d+1≤j.val+1 := by omega
    simp [hj,hL]
  · rw [buildAdj_left _ _ _ _ hd _ _ i.isLt]
    have hs : d+1+j.val-(d+1)=j.val := by omega
    simp [hs,hB,ts] <;> rfl
  · rw [buildAdj_right _ _ _ _ hd _ _ i.isLt, mixedBits_off _ _ _ (Or.inr rfl)]
    have h := (sym _ _).not.mpr (R i).property.2
    simp [h]
  · rw [buildAdj_right _ _ _ _ hd _ _ i.isLt, mixedBits_read]
    have hj : ¬d+1≤j.val+1 := by omega
    simp [hj,maskList_read,hB,ts, sym (R i).val (L j).val]
  · rw [buildAdj_right _ _ _ _ hd _ _ i.isLt, mixedBits_off _ _ _ (Or.inl (by omega))]
    have hh : d+1+j.val-(d+1)=j.val := by omega
    simp [hh,hM] <;> rfl

#print axioms hostAdj_slots
end Erdos151N63
