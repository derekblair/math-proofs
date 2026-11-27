import FamilyPrefix

namespace IU
def ElementaryClosed (F : Finset (Finset Nat)) (n : Nat) : Prop :=
  ∀ B∈F, ∀ i j : Nat, i<j → j<n → i∉B → j∈B → insert i (B.erase j)∈F

private theorem early_subset {B C : Finset Nat} {t : Nat}
    (h : ∀ x∈B\C, t≤x) : below B t ⊆ below C t := by
  intro x hx
  obtain ⟨b,lt⟩ := Finset.mem_filter.mp hx
  apply Finset.mem_filter.mpr
  refine ⟨?_,lt⟩
  by_contra c
  have H := h x (Finset.mem_sdiff.mpr ⟨b,c⟩)
  omega

private theorem shift_count (B : Finset Nat) (i j t : Nat) (iB : i∉B) (jB : j∈B) (lt : i<j) :
    pr (insert i (B.erase j)) t =
      pr B t + (if i<t then 1 else 0) - (if j<t then 1 else 0) := by
  have e : below (B.erase j) t = (below B t).erase j := by
    ext x
    simp [and_assoc]
  have iE : i∉below (B.erase j) t := fun h =>
    iB (Finset.mem_of_mem_erase (Finset.mem_filter.mp h).1)
  have V : below (insert i (B.erase j)) t =
      if i<t then insert i (below (B.erase j) t) else below (B.erase j) t := by
    exact Finset.filter_insert _ _ _
  change (below (insert i (B.erase j)) t).card = _
  rw [V,e]
  by_cases h : i<t <;> by_cases g : j<t
  · simp only [h,g,ite_true]
    rw [Finset.card_insert_of_notMem,Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨jB,g⟩)]
    · change pr B t-1+1 = pr B t+1-1
      have P : 0 < pr B t := Finset.card_pos.mpr ⟨j,Finset.mem_filter.mpr ⟨jB,g⟩⟩
      omega
    · rwa [←e]
  · have j0 : j∉below B t := fun hj => g (Finset.mem_filter.mp hj).2
    simp only [h,g,ite_true,ite_false,not_false_eq_true]
    rw [Finset.erase_eq_of_notMem j0,Finset.card_insert_of_notMem
      (fun q => iB (Finset.mem_filter.mp q).1)]
    rfl
  · omega
  · have j0 : j∉below B t := fun hj => g (Finset.mem_filter.mp hj).2
    simp only [h,g,ite_false]
    rw [Finset.erase_eq_of_notMem j0]
    rfl

theorem prefix_closed_of_elementary (F : Finset (Finset Nat)) {n : Nat}
    (bounded : ∀ B∈F, B ⊆ Finset.range n) (closed : ElementaryClosed F n) :
    ClosedUnderPrefix F n := by
  intro B bF C cRange cB dom
  have main (k : Nat) : ∀ B∈F, (B\C).card=k → C.card=B.card →
      (∀ t≤n, pr B t≤pr C t) → C∈F := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro B bF kB cB dom
      by_cases bc : B⊆C
      · have eq := Finset.eq_of_subset_of_card_le bc (by rw [cB])
        exact eq ▸ bF
      have bDif : (B\C).Nonempty := by
        obtain ⟨x,bx,cx⟩ := Finset.not_subset.mp bc
        exact ⟨x,Finset.mem_sdiff.mpr ⟨bx,cx⟩⟩
      have nc : ¬ C⊆B := fun cb => bc (Finset.eq_of_subset_of_card_le cb (by rw [cB])).symm.subset
      have cDif : (C\B).Nonempty := by
        obtain ⟨x,cx,bx⟩ := Finset.not_subset.mp nc
        exact ⟨x,Finset.mem_sdiff.mpr ⟨cx,bx⟩⟩
      let i := (C\B).min' cDif
      let j := (B\C).min' bDif
      have iC : i∈C ∧ i∉B := Finset.mem_sdiff.mp (Finset.min'_mem _ cDif)
      have jB : j∈B ∧ j∉C := Finset.mem_sdiff.mp (Finset.min'_mem _ bDif)
      have jn : j<n := Finset.mem_range.mp (bounded B bF jB.1)
      have loB (x : Nat) (h : x∈B\C) : j≤x := Finset.min'_le _ x h
      have loC (x : Nat) (h : x∈C\B) : i≤x := Finset.min'_le _ x h
      have lij : i<j := by
        by_contra wrong
        have eq : i≠j := fun e => iC.2 (e.symm ▸ jB.1)
        have S : below C (j+1) ⊆ below B (j+1) :=
          early_subset (fun x hx => by have L := loC x hx; omega)
        have pp : pr C (j+1)<pr B (j+1) := by
          apply Finset.card_lt_card
          refine Finset.ssubset_iff_subset_ne.mpr ⟨S,?_⟩
          intro E
          have j0 : j∈below B (j+1) := Finset.mem_filter.mpr ⟨jB.1,by omega⟩
          rw [←E] at j0
          exact jB.2 (Finset.mem_filter.mp j0).1
        exact (not_le_of_gt pp) (dom _ (by omega))
      let P := insert i (B.erase j)
      have pF : P∈F := closed B bF i j lij jn iC.2 jB.1
      have cardP : P.card=B.card := by
        have ie : i∉B.erase j := fun e => iC.2 (Finset.mem_of_mem_erase e)
        change (insert i (B.erase j)).card = _
        rw [Finset.card_insert_of_notMem ie,Finset.card_erase_of_mem jB.1]
        have pe : 0<B.card := Finset.card_pos.mpr ⟨j,jB.1⟩
        omega
      have less : (P\C).card<k := by
        have E : P\C = (B\C).erase j := by
          ext x
          simp [P]
          grind
        rw [E,←kB]
        apply Finset.card_lt_card
        exact Finset.erase_ssubset (Finset.mem_sdiff.mpr jB)
      apply ih _ less P pF rfl (cB.trans cardP.symm)
      intro t tn
      change pr (insert i (B.erase j)) t≤_
      rw [shift_count B i j t iC.2 jB.1 lij]
      have H := dom t tn
      by_cases it : i<t <;> by_cases jt : j<t
      · simp [it,jt,H]
      · rw [if_pos it,if_neg jt,Nat.sub_zero]
        have S : below B t ⊆ below C t := early_subset (fun x hx => by have h := loB x hx; omega)
        have pp : pr B t<pr C t := by
          apply Finset.card_lt_card
          refine Finset.ssubset_iff_subset_ne.mpr ⟨S,?_⟩
          intro E
          have i0 : i∈below C t := Finset.mem_filter.mpr ⟨iC.1,it⟩
          rw [←E] at i0
          exact iC.2 (Finset.mem_filter.mp i0).1
        omega
      · omega
      · simp [it,jt,H]
  exact main _ B bF rfl cB dom

#print axioms prefix_closed_of_elementary
end IU
