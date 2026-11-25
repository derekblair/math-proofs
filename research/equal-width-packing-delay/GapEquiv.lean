import GapRestore
import EqualWidthAnswer

namespace CoverCutoff
open Finset FussCover

variable {h : ℕ} (hh : 2≤h)

lemma recovery_right (S : BallotSet h) :
    gapToBallot hh (ballotToGap S hh) = S := by
  apply Subtype.ext
  change univ.image (coreUp hh (ballotToGap S hh)) = S.val
  have E : coreUp hh (ballotToGap S hh) = ballotUp S := by
    funext i
    have hi := i.isLt
    apply Fin.ext
    change smallU (readRank (restored S)) (i.val+2)-3 = (ballotUp S i).val
    rw [restoredU S (by omega),restoreU_other S _ (by omega) (by omega)]
    have eq : (⟨i.val+2-2,by omega⟩ : Fin h) = i := Fin.ext (by change i.val+2-2=i.val; omega)
    rw [eq]
    omega
  rw [E]
  exact image_orderEmbOfFin_univ _ _

lemma recovery_left (p : GapPack h) :
    ballotToGap (gapToBallot hh p) hh = p := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro a
  let r := p.val.val
  let S := gapToBallot hh p
  have N := smallSize (j:=h+1) (by omega)
  have ha := a.isLt
  have e := gap_first_ranks hh p
  have f := final_rank hh p.val
  apply Fin.ext
  change (restored S a).val = (r a).val
  rw [←readRank_fin,←readRank_fin,readRestored S ha]
  by_cases ev : a.val%2=0
  · rw [show a.val=uPos (a.val/2) by unfold uPos; omega,restoreRank_U]
    change restoreU S (a.val/2) = smallU (readRank r) (a.val/2)
    by_cases e0 : a.val/2=0
    · rw [e0,restoreU_zero,e.1]
    by_cases e1 : a.val/2=1
    · rw [e1,restoreU_one,e.2.1]
    let i : Fin h := ⟨a.val/2-2,by omega⟩
    rw [restoreU_other S _ (by omega) (by omega)]
    have C : ballotUp S i=coreUp hh p i := congrFun (gapUp_order hh p) i
    change 3+(ballotUp S i).val=smallU (readRank r) (a.val/2)
    rw [C]
    have I : i.val+2=a.val/2 := by dsimp [i]; omega
    have lo := (upRange hh p i).1
    change 3≤smallU (readRank r) (i.val+2) at lo
    change 3+(smallU (readRank r) (i.val+2)-3)=smallU (readRank r) (a.val/2)
    rw [I] at *
    omega
  · rw [show a.val=vPos (a.val/2) by unfold vPos; omega,restoreRank_V]
    change restoreV S (a.val/2) = smallV (readRank r) (a.val/2)
    by_cases e0 : a.val/2=0
    · rw [e0,restoreV_zero,e.2.2]
    by_cases el : a.val/2=h+1
    · rw [el,restoreV_last,f]
    let i : Fin h := ⟨a.val/2-1,by omega⟩
    rw [restoreV_other S _ (by omega) (by omega)]
    have C : ballotDown S i=coreDown hh p i := congrFun (gapDown_order hh p) i
    change 3+(ballotDown S i).val=smallV (readRank r) (a.val/2)
    rw [C]
    have I : i.val+1=a.val/2 := by dsimp [i]; omega
    have lo := (downRange hh p i).1
    change 3≤smallV (readRank r) (i.val+1) at lo
    change 3+(smallV (readRank r) (i.val+1)-3)=smallV (readRank r) (a.val/2)
    rw [I] at *
    omega

noncomputable def gapEquiv : GapPack h ≃ BallotSet h :=
  ⟨gapToBallot hh, (fun S => ballotToGap S hh), recovery_left hh, recovery_right hh⟩

theorem exact_delayed_difference :
    packCount (delayed h hh) 3 (h+1) =
      packCount patternA 2 (h+1) + catalan h := by
  rw [first_difference_eq_gap_count hh,Nat.card_congr (gapEquiv hh),ballot_count h]

#print axioms exact_delayed_difference
end CoverCutoff
