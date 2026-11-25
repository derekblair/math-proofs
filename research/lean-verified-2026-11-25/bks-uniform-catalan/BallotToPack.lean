import PackToBallot

namespace FussCover
open Finset
variable {z h j : ℕ} (hj : 0<j) (hz : 0<z)
variable (S : BallotSet j)

def ballotU (i : Fin j) : Fin (2*j) := S.val.orderEmbOfFin S.property.1 i
def ballotD (i : Fin j) : Fin (2*j) := (S.valᶜ : Finset _).orderEmbOfFin (comp_card _ S.property.1) i

lemma U_strict : StrictMono (ballotU S) := (S.val.orderEmbOfFin S.property.1).strictMono
lemma D_strict : StrictMono (ballotD S) := ((S.valᶜ : Finset _).orderEmbOfFin (comp_card _ S.property.1)).strictMono
lemma ballotCross (i : Fin j) : ballotU S i < ballotD S i :=
  (ballot_iff_orders _ S.property.1).mp S.property.2 i

def mRank : Labels z h j → Fin (n z h j)
  | .inl u => ⟨u.val,by have := u.isLt; have e := n_eq_head_core (z:=z) (h:=h) hj; omega⟩
  | .inr (.inl t) =>
    if lt : t.val<j then raise hj (ballotU S (⟨t.val,lt⟩ : Fin j).rev)
    else ⟨hN z h j,by have e := n_eq_head_core (z:=z) (h:=h) hj; omega⟩
  | .inr (.inr t) =>
    if zt : t.val=0 then ⟨hN z h j+2*j+1,by have e := n_eq_head_core (z:=z) (h:=h) hj; omega⟩
    else raise hj (ballotD S (⟨t.val-1,by have := t.isLt; omega⟩ : Fin j).rev)

lemma mRankHead (u : Fin (hN z h j)) :
    (mRank hj S (.inl u)).val=u.val := rfl
lemma mRankA0 : (mRank (z:=z) (h:=h) hj S (.inr (.inl (Fin.last j)))).val=hN z h j := by
  unfold mRank; simp
lemma mRankB0 : (mRank (z:=z) (h:=h) hj S (.inr (.inr 0))).val=hN z h j+2*j+1 := by
  unfold mRank; simp
lemma mRankA (i : Fin j) : mRank hj S (.inr (.inl (aI i))) = raise (z:=z) (h:=h) hj (ballotU S i) := by
  change (if lt : (aI i).val<j then raise hj (ballotU S (⟨(aI i).val,lt⟩ : Fin j).rev)
    else _) = raise hj (ballotU S i)
  have a : (aI i).val<j := i.rev.isLt
  rw [dite_eq_left a]
  congr 2
  change (⟨i.rev.val,i.rev.isLt⟩ : Fin j).rev=i
  exact Fin.rev_rev i
lemma mRankB (i : Fin j) : mRank hj S (.inr (.inr (bI i))) = raise (z:=z) (h:=h) hj (ballotD S i) := by
  change (if zt : (bI i).val=0 then ⟨hN z h j+2*j+1,by have e := n_eq_head_core (z:=z) (h:=h) hj; omega⟩ else
    raise hj (ballotD S (⟨(bI i).val-1,by have := (bI i).isLt; omega⟩ : Fin j).rev)) =
    raise hj (ballotD S i)
  have b : (bI i).val≠0 := Nat.ne_of_gt (show 0 < (bI i).val from bI_pos i)
  rw [dite_eq_right b]
  congr 2
  have e : (⟨(bI i).val-1,by change i.rev.val+1-1<j; omega⟩ : Fin j)=i.rev := by
    apply Fin.ext
    simp [bI]
  rw [e,Fin.rev_rev]

lemma mRank_surj : Function.Surjective (mRank (z:=z) (h:=h) hj S) := by
  intro x
  by_cases lo : x.val < hN z h j
  · exact ⟨.inl ⟨x.val,lo⟩,Fin.ext rfl⟩
  by_cases eq : x.val = hN z h j
  · exact ⟨.inr (.inl (Fin.last j)),Fin.ext ((mRankA0 hj S).trans eq.symm)⟩
  by_cases hi : x.val < hN z h j+2*j+1
  · let a := lower x (by omega) hi
    by_cases mem : a ∈ S.val
    · have inrange : a ∈ Set.range (S.val.orderEmbOfFin S.property.1) := by
        rw [range_orderEmbOfFin]; exact mem
      obtain ⟨i,e⟩ := inrange
      refine ⟨.inr (.inl (aI i)),?_⟩
      rw [mRankA]
      change raise hj (S.val.orderEmbOfFin S.property.1 i)=x
      rw [e]; exact raise_lower hj _ _ _
    · have inrange : a ∈ Set.range ((S.valᶜ : Finset _).orderEmbOfFin (comp_card _ S.property.1)) := by
        rw [range_orderEmbOfFin]; exact Finset.mem_compl.mpr mem
      obtain ⟨i,e⟩ := inrange
      refine ⟨.inr (.inr (bI i)),?_⟩
      rw [mRankB]
      change raise hj ((S.valᶜ : Finset _).orderEmbOfFin (comp_card _ S.property.1) i)=x
      rw [e]; exact raise_lower hj _ _ _
  · have e := n_eq_head_core (z:=z) (h:=h) hj
    have xlt := x.isLt
    have high : x.val=hN z h j+2*j+1 := by omega
    exact ⟨.inr (.inr 0),Fin.ext ((mRankB0 hj S).trans high.symm)⟩

noncomputable def ranksOfBallot : Equiv.Perm (Fin (n z h j)) :=
  Equiv.ofBijective _ ((mRank_surj (z:=z) (h:=h) hj S).comp (posEquiv hj hz).symm.surjective).bijective_of_finite

@[simp] lemma rankOfPos (u : Labels z h j) :
    ranksOfBallot hj hz S (posEquiv hj hz u) = mRank hj S u := by
  change mRank hj S ((posEquiv hj hz).symm (posEquiv hj hz u))=mRank hj S u
  rw [Equiv.symm_apply_apply]

lemma ballot_head (u : Fin (hN z h j)) :
    (ranksOfBallot hj hz S (hAt hj hz u)).val=u.val := by
  change (ranksOfBallot hj hz S (posEquiv hj hz (.inl u))).val=u.val
  rw [rankOfPos,mRankHead]
lemma ballot_a0 :
    (ranksOfBallot (z:=z) (h:=h) hj hz S (A hj (Fin.last j))).val=hN z h j := by
  change (ranksOfBallot hj hz S (posEquiv hj hz (.inr (.inl (Fin.last j))))).val=hN z h j
  rw [rankOfPos,mRankA0]
lemma ballot_b0 :
    (ranksOfBallot (z:=z) (h:=h) hj hz S (B hj 0)).val=hN z h j+2*j+1 := by
  change (ranksOfBallot hj hz S (posEquiv hj hz (.inr (.inr 0)))).val=hN z h j+2*j+1
  rw [rankOfPos,mRankB0]
lemma ballot_a (i : Fin j) :
    ranksOfBallot (z:=z) (h:=h) hj hz S (A hj (aI i))=raise hj (ballotU S i) := by
  change ranksOfBallot hj hz S (posEquiv hj hz (.inr (.inl (aI i))))=_
  rw [rankOfPos,mRankA]
lemma ballot_b (i : Fin j) :
    ranksOfBallot (z:=z) (h:=h) hj hz S (B hj (bI i))=raise hj (ballotD S i) := by
  change ranksOfBallot hj hz S (posEquiv hj hz (.inr (.inr (bI i))))=_
  rw [rankOfPos,mRankB]

end FussCover
