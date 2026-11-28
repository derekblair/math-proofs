import N63FiveSafe
import N63FiveMatchCert
import N63HostDegree

namespace Erdos151N63
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : V → V → Prop) [DecidableRel G]

theorem five_blocks_witness (w : V)
    (L : Fin 5 ≃ {z : V // G w z}) (R : Fin 4 ≃ {z : V // z≠w ∧ ¬G w z})
    (f : Fin 5 → Fin 16) (fm : ∀ i j : Fin 5, i.val≤j.val → (f i).val≤(f j).val)
    (hbits : ∀ (i : Fin 5) (j : Fin 4), (f i).val.testBit j.val = decide (G (L i).val (R j).val))
    (sym : ∀ a b, G a b ↔ G b a) (irr : ∀ v, ¬G v v)
    (tf : ∀ v x y, G v x → G v y → ¬G x y)
    (hL : ∀ i j, ¬G (L i).val (L j).val)
    (hD : fullDeg G w=5) (hmin : ∀ v, 2≤fullDeg G v) (hmax : ∀ v, fullDeg G v≤5)
    (dense : 30≤∑ v : V,fullDeg G v) : TenWitness G := by
  let RR (i j : Nat) : Bool := if hi : i<4 then if hj : j<4 then
    decide (G (R ⟨i,hi⟩).val (R ⟨j,hj⟩).val) else false else false
  obtain ⟨h,hh,hdec⟩ := right_code_exists 4 RR
    (by intro i j; by_cases hi : i<4 <;> by_cases hj : j<4 <;> simp [RR,hi,hj,sym])
    (by intro i; by_cases hi : i<4 <;> simp [RR,hi,irr])
  have hh' : h<64 := hh
  let H := graphOfCode 4 h
  have rep (i j : Fin 4) : adj H i.val j.val = decide (G (R i).val (R j).val) :=
    (hdec _ i.isLt _ j.isLt).trans (by simp [RR,i.isLt,j.isLt])
  have ht : tfRight 4 H = true := by
    apply tfRight_of_bits
    · exact fun j hj => rightBits_width _ _ _ hj
    · intro a b j ha hb hj hab haj
      have a' := rep ⟨a,ha⟩ ⟨b,hb⟩
      have b' := rep ⟨a,ha⟩ ⟨j,hj⟩
      rw [hab] at a'
      rw [haj] at b'
      have hz := tf _ _ _ (of_decide_eq_true a'.symm) (of_decide_eq_true b'.symm)
      exact (rep ⟨b,hb⟩ ⟨j,hj⟩).trans (by simp [hz])
  have hm (i : Fin 5) : allowed 4 H (f i)=true := by
    apply allowed_of_bits
    · exact fun j hj => rightBits_width _ _ _ hj
    · intro a b ha hb hLa hab
      have a' := hbits i ⟨a,ha⟩
      have b' := rep ⟨a,ha⟩ ⟨b,hb⟩
      rw [hLa] at a'
      rw [hab] at b'
      have hz := tf _ _ _ ((sym _ _).mp (of_decide_eq_true a'.symm)) (of_decide_eq_true b'.symm)
      exact (hbits i ⟨b,hb⟩).trans (by simp [hz])
  by_cases Hgood : ∃ y : Fin 4, rightGood5 H y.val (fullDeg G (R y).val)=true
  · obtain ⟨y,hy⟩ := Hgood
    exact witnessFive_good G w R hD H rep sym irr y (hmax _) hy
  let T (i : Fin 4) : Fin 4 := ⟨fullDeg G (R i).val-2,by have := hmax (R i).val; omega⟩
  have heT (i : Fin 4) : (T i).val+2=fullDeg G (R i).val := by
    change fullDeg G (R i).val-2+2=_
    have := hmin (R i).val
    omega
  have heR (i : Fin 4) : deg H 4 i.val = rightDeg G (fun j => (R j).val) i := by
    change pop 4 (mask H i.val) = _
    rw [pop_sum,rightDeg]
    apply Finset.sum_congr rfl
    intro j _
    change (if adj H i.val j.val then 1 else 0) = _
    simp [rep]
  have hraw : 30+((List.range 4).map (deg H 4)).sum ≤
      10+2*((List.finRange 4).map fun i => (T i).val+2).sum := by
    have hb := right_degree_balance G w L R sym (irr w) hL hD
    rw [←finRange_vals 4,List.map_map, ←List.sum_toFinset _ (List.nodup_finRange _),
      List.toFinset_finRange,←List.sum_toFinset _ (List.nodup_finRange _),List.toFinset_finRange]
    simp only [Function.comp_apply,heR,heT]
    omega
  have bad (y : Fin 4) : rightGood5 H y.val ((T y).val+2)=false := by
    rw [heT]
    exact Bool.eq_false_of_not_eq_true (fun hh => Hgood ⟨y,hh⟩)
  obtain ⟨hhm,hd3⟩ := fiveTotals_all h hh' T ht hraw bad
  have hz3 (j : Fin 4) : fullDeg G (R j).val=3 := by
    rw [←heT,hd3]
  let ts := (List.finRange 5).map fun i => (f i).val
  have hdeg := hostDegree_filter G w (m:=15) H f L R sym (irr w) hL rep hbits (n:=10)
    (by decide) hD hmin hmax dense
  have hright (j : Fin 4) : pop 4 (mask H j.val) +
      (ts.filter (·.testBit j.val)).length = 3 := by
    rw [pop_sum]
    have h := deg_over_slots G w (R j).val (irr w) L R
    have hz := (sym (R j).val w).not.mpr (R j).property.2
    simp only [if_neg hz,Nat.zero_add,hz3] at h
    rw [Nat.add_comm]
    have h1 : (ts.filter (·.testBit j.val)).length =
        ∑ i : Fin 5, if G (R j).val (L i).val then 1 else 0 := by
      rw [show (ts.filter (·.testBit j.val)).length = ∑ i : Fin 5, if (f i).val.testBit j.val then 1 else 0 from leftsum_bits 5 4 f j.val]
      apply Finset.sum_congr rfl
      intro i _
      simp [hbits,sym (L i).val (R j).val]
    have h2 : (∑ i : Fin 4, if (mask H j.val).testBit i.val then 1 else 0) =
        ∑ i : Fin 4, if G (R j).val (R i).val then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      change (if adj H j.val i.val then 1 else 0) = _
      simp [rep]
    rw [h1,h2]
    exact h.symm
  have htail : ((rawDegrees 5 4 H ts).drop 6).all (·==3)=true := by
    unfold rawDegrees
    change ((((5 :: ts.map (fun m => 1+pop 4 m)) ++ _) : List Nat).drop 6).all (·==3) = true
    have hsz : (5 :: ts.map (fun m => 1+pop 4 m)).length=6 := by simp [ts]
    rw [←hsz,List.drop_left]
    rw [List.all_eq_true]
    intro a ha
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
    have h := hright ⟨j,List.mem_range.mp hj⟩
    simp [h]
  have hmem := mem_matchRows h f fm hm hdeg htail
  obtain ⟨p,hrow,hcert⟩ := matching_pivots h hhm _ hmem
  let IX := indexEquiv 5 4 10 (by decide)
  let sl := slotEquiv G w (irr w) L R
  apply chart_to_ten_witness G p hcert (IX.symm.trans sl)
  intro i j
  have hi : indexVal (IX.symm i)=i.val := congrArg Fin.val (IX.apply_symm_apply i)
  have hj : indexVal (IX.symm j)=j.val := congrArg Fin.val (IX.apply_symm_apply j)
  have az := hostAdj_slots G w H f L R sym (irr w) hL rep hbits (IX.symm i) (IX.symm j)
  rw [hi,hj,hrow] at az
  rw [az]
  simp [IX,sl,slotEquiv]

#print axioms five_blocks_witness
end Erdos151N63
