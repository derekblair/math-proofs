import LiftRank

namespace CoverCutoff

lemma kept_key {h j : ℕ} (hj : 1≤j) (p : Equiv.Perm (Fin (SmallN j))) (flip : Bool)
    {a : ℕ} (ha : a<SmallN j) :
    bigKey (h:=h) p flip (keptIndex h a)=3*(liftBase h j+readRank p a) := by
  have hN := smallSize hj
  unfold keptIndex
  split_ifs with ha'
  · rw [bigKey_A]
    unfold keyA
    rw [if_neg (by omega),show h-1+a/2-(h-1)=a/2 by omega]
    unfold mainU smallU uPos
    rw [show 2*(a/2)=a by omega]
  · rw [bigKey_C]
    unfold keyC
    rw [if_pos (by omega)]
    unfold mainV smallV vPos
    rw [show 2*(a/2)+1=a by omega]

lemma lift_comparison_on_kept {h j : ℕ} (hh : 2≤h) (hj : 1≤j)
    (p : Equiv.Perm (Fin (SmallN j))) (flip : Bool) {a b : ℕ}
    (ha : a<SmallN j) (hb : b<SmallN j) :
    readRank (liftRanks (h:=h) p flip) (keptIndex h a) <
      readRank (liftRanks (h:=h) p flip) (keptIndex h b) ↔
      readRank p a < readRank p b := by
  let A := embedSmall h j hh hj ⟨a,ha⟩
  let B := embedSmall h j hh hj ⟨b,hb⟩
  have ea : keptIndex h a = A.val := rfl
  have eb : keptIndex h b = B.val := rfl
  rw [ea,eb,readRank_fin,readRank_fin]
  change liftRanks p flip A < liftRanks p flip B ↔ _
  rw [liftRanks,rankKey_iff,Prod.Lex.lt_iff]
  change (bigKey (h:=h) p flip A.val < bigKey (h:=h) p flip B.val ∨
    bigKey (h:=h) p flip A.val=bigKey (h:=h) p flip B.val ∧ A.val < B.val) ↔ _
  rw [←ea,←eb,kept_key hj p flip ha,kept_key hj p flip hb]
  constructor
  · rintro (hl|⟨he,hlt⟩)
    · omega
    · have heq : readRank p a=readRank p b := by omega
      have hne := readRank_inj p ha hb heq
      have hv := congrArg (keptIndex h) hne
      omega
  · intro hlt
    left
    omega

theorem restrict_lift {h j : ℕ} (hh : 2≤h) (hj : 1≤j)
    (p : Equiv.Perm (Fin (SmallN j))) (flip : Bool) :
    restrictSmall h j hh hj (liftRanks p flip)=p := by
  apply same_comparisons
  intro a b
  have h := (restrict_comparison hh hj (liftRanks p flip) a.isLt b.isLt).trans
    (lift_comparison_on_kept hh hj p flip a.isLt b.isLt)
  rw [readRank_fin,readRank_fin,readRank_fin,readRank_fin] at h
  exact h

#print axioms restrict_lift
end CoverCutoff
