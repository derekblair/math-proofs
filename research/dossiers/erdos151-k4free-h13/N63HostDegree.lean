import N63DegreeSums

namespace Erdos151N63
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : V→V→Prop) [DecidableRel G]

theorem hostDegree_filter (w : V) {d q n m : Nat} (H : Array Nat) (f : Fin d → Fin (2^q))
    (L : Fin d ≃ {z : V // G w z}) (R : Fin q ≃ {z : V // z≠w ∧ ¬G w z})
    (sym : ∀ a b, G a b ↔ G b a) (irr : ¬G w w)
    (hL : ∀ i j, ¬G (L i).val (L j).val)
    (hM : ∀ i j : Fin q, adj H i.val j.val = decide (G (R i).val (R j).val))
    (hB : ∀ i j, (f i).val.testBit j.val = decide (G (L i).val (R j).val))
    (hn : d+q+1=n) (hD : fullDeg G w=d)
    (hmin : ∀ v, 2 ≤ fullDeg G v) (hmax : ∀ v, fullDeg G v ≤ d)
    (dense : 2*m ≤ ∑ v : V, fullDeg G v) :
    rawDegreeOK n m d q H ((List.finRange d).map fun i => (f i).val) = true := by
  have left (i : Fin d) : 1+pop q (f i).val = fullDeg G (L i).val := by
    rw [deg_over_slots G w _ irr L R,pop_sum]
    simp only [if_pos ((sym _ _).mp (L i).property),hL,ite_false,Finset.sum_const_zero,Nat.add_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp [hB]
  have right (j : Fin q) : pop q (mask H j.val) +
      (((List.finRange d).map fun i => (f i).val).filter (·.testBit j.val)).length =
      fullDeg G (R j).val := by
    rw [deg_over_slots G w _ irr L R,pop_sum,leftsum_bits]
    have hz := (sym (R j).val w).not.mpr (R j).property.2
    simp only [if_neg hz,Nat.zero_add]
    rw [Nat.add_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      simp [hB,sym (L i).val (R j).val]
    · apply Finset.sum_congr rfl
      intro i _
      change (if adj H j.val i.val then 1 else 0) = _
      simp [hM]
  let ld := (List.finRange d).map fun i => fullDeg G (L i).val
  let rd := (List.finRange q).map fun j => fullDeg G (R j).val
  have he : rawDegrees d q H ((List.finRange d).map fun i => (f i).val) =
      fullDeg G w :: (ld ++ rd) := by
    unfold rawDegrees
    rw [←finRange_vals q]
    simp only [List.map_map]
    have h1 : ((fun m => 1+pop q m) ∘ (fun i => (f i).val)) =
        (fun i => fullDeg G (L i).val) := funext left
    have h2 : ((fun j =>
        pop q (mask H j) + (((List.finRange d).map fun i => (f i).val).filter
          (·.testBit j)).length) ∘ (Fin.val : Fin q → Nat)) =
        (fun j => fullDeg G (R j).val) := funext right
    rw [h1,h2,hD]
    simp [ld,rd]
  have cal : (fullDeg G w :: (ld ++ rd)).length = n := by
    simp [ld,rd,hn]
  have bounds : (fullDeg G w :: (ld ++ rd)).all (fun a => 2≤a && a≤d) = true := by
    rw [List.all_eq_true]
    intro a ha
    rcases List.mem_cons.mp ha with ha|ha
    · subst a
      simp [hmin,hmax]
    · rcases List.mem_append.mp ha with h|h
      · obtain ⟨v,_,rfl⟩ := List.mem_map.mp h
        simp [hmin,hmax]
      · obtain ⟨v,_,rfl⟩ := List.mem_map.mp h
        simp [hmin,hmax]
  have hsum : (fullDeg G w :: (ld ++ rd)).sum = ∑ v : V, fullDeg G v := by
    rw [sum_over_slots G w irr L R]
    simp only [List.sum_cons,List.sum_append,ld,rd]
    rw [← List.sum_toFinset _ (List.nodup_finRange _),List.toFinset_finRange,
      ← List.sum_toFinset _ (List.nodup_finRange _),List.toFinset_finRange]
    omega
  unfold rawDegreeOK
  simp [he,cal,bounds,hsum,dense]

#print axioms hostDegree_filter
end Erdos151N63
