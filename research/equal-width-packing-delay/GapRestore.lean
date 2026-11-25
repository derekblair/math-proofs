import GapInverse

namespace CoverCutoff
open Finset FussCover
variable {h : ℕ} (S : BallotSet h)

def restoreRank (v : ℕ) : ℕ :=
  if v%2=0 then restoreU S (v/2) else restoreV S (v/2)
@[simp] lemma restoreRank_U (i : ℕ) : restoreRank S (uPos i)=restoreU S i := by
  unfold restoreRank uPos
  rw [if_pos (by omega), show 2*i/2=i by omega]
@[simp] lemma restoreRank_V (i : ℕ) : restoreRank S (vPos i)=restoreV S i := by
  unfold restoreRank vPos
  rw [if_neg (by omega), show (2*i+1)/2=i by omega]

lemma restoreRank_lt (i : Fin (SmallN (h+1))) : restoreRank S i.val < SmallN (h+1) := by
  have N := smallSize (j:=h+1) (by omega)
  have hi := i.isLt
  unfold restoreRank
  split_ifs
  · exact (restoreU_lt S _ (by omega)).trans_le (by omega)
  · exact (restoreV_lt S _ (by omega)).trans_le (by omega)

def restoreFn (i : Fin (SmallN (h+1))) : Fin (SmallN (h+1)) :=
  ⟨restoreRank S i.val,restoreRank_lt S i⟩

lemma restoreFn_inj : Function.Injective (restoreFn S) := by
  intro i j e
  have N := smallSize (j:=h+1) (by omega)
  have hi := i.isLt
  have hj := j.isLt
  have ep : restoreRank S i.val=restoreRank S j.val := congrArg Fin.val e
  apply Fin.ext
  unfold restoreRank at ep
  split_ifs at ep with a b b
  · have eq : i.val/2=j.val/2 := by
      by_contra! ne
      rcases lt_or_gt_of_ne ne with x|x
      · exact (restoreU_strict S _ _ x (by omega)).ne ep
      · exact (restoreU_strict S _ _ x (by omega)).ne ep.symm
    omega
  · exact (restore_disjoint S _ _ (by omega) (by omega) ep).elim
  · exact (restore_disjoint S _ _ (by omega) (by omega) ep.symm).elim
  · have eq : i.val/2=j.val/2 := by
      by_contra! ne
      rcases lt_or_gt_of_ne ne with x|x
      · exact (restoreV_strict S _ _ x (by omega)).ne ep
      · exact (restoreV_strict S _ _ x (by omega)).ne ep.symm
    omega

noncomputable def restored : Equiv.Perm (Fin (SmallN (h+1))) :=
  Equiv.ofBijective (restoreFn S) ⟨restoreFn_inj S,
    Finite.injective_iff_surjective.mp (restoreFn_inj S)⟩

lemma readRestored {a : ℕ} (ha:a<SmallN (h+1)) :
    readRank (restored S) a=restoreRank S a := by
  rw [show readRank (restored S) a=(restored S ⟨a,ha⟩).val from readRank_fin _ ⟨a,ha⟩]
  rfl

lemma restoredU {i : ℕ} (hi : i<h+2) :
    smallU (readRank (restored S)) i=restoreU S i := by
  unfold smallU
  rw [readRestored S (by have := smallSize (j:=h+1) (by omega); unfold uPos; omega),restoreRank_U]

lemma restoredV {i : ℕ} (hi : i<h+2) :
    smallV (readRank (restored S)) i=restoreV S i := by
  unfold smallV
  rw [readRestored S (by have := smallSize (j:=h+1) (by omega); unfold vPos; omega),restoreRank_V]

lemma restored_packs : Packs patternA 2 (h+1) (restored S) := by
  apply (small_packs_iff _).mpr
  refine ⟨?_,?_,?_⟩
  · intro i _ hi
    rw [restoredU S (by omega),restoredU S (show i+1<h+2 by omega)]
    exact restoreU_strict S i (i+1) (by omega) (by omega)
  · intro i _ hi
    rw [restoredV S (by omega),restoredV S (show i+1<h+2 by omega)]
    exact restoreV_strict S i (i+1) (by omega) (by omega)
  · intro i hi
    rw [restoredU S (by omega),restoredV S (by omega)]
    exact restored_cross S i hi

noncomputable def ballotToGap (hh : 2≤h) : GapPack h := by
  refine ⟨⟨restored S,restored_packs S⟩,?_⟩
  change smallV (readRank (restored S)) 0 < smallU (readRank (restored S)) 2
  rw [restoredV S (by omega),restoredU S (by omega)]
  rw [restoreV_zero,restoreU_other S 2 (by omega) (by omega)]
  omega

#print axioms ballotToGap
end CoverCutoff
