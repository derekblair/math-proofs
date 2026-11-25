import GapEndpoints
import CoreBallot
namespace CoverCutoff

variable {h : ℕ} (hh : 2≤h) (p : GapPack h)

def upPosition (i : Fin h) := uPos (i.val+2)
def downPosition (i : Fin h) := vPos (i.val+1)

include hh in
lemma upRange (i : Fin h) :
    3 ≤ readRank p.val.val (upPosition i) ∧
    readRank p.val.val (upPosition i) < 2*h+3 := by
  have N := smallSize (j:=h+1) (by omega)
  have hi := i.isLt
  have h0 := gap_first_ranks hh p
  have h1 := final_rank hh p.val
  have r := gap_row p
  have lo := p.prop.trans_le (asc_le' r.1 (k:=i.val+2) (by omega) (by omega))
  have hi' := r.2.2 h (by omega)
  have vs : smallV (readRank p.val.val) h ≤ smallV (readRank p.val.val) (h+1) := asc_le' r.2.1 (by omega) (by omega)
  have le : smallU (readRank p.val.val) (i.val+2) ≤ smallU (readRank p.val.val) (h+1) :=
    asc_le' r.1 (by omega) (by omega)
  unfold upPosition
  change 3≤smallU (readRank p.val.val) (i.val+2) ∧
    smallU (readRank p.val.val) (i.val+2)<2*h+3
  omega

include hh in
lemma downRange (i : Fin h) :
    3 ≤ readRank p.val.val (downPosition i) ∧
    readRank p.val.val (downPosition i) < 2*h+3 := by
  have hi := i.isLt
  have h0 := gap_first_ranks hh p
  have h1 := final_rank hh p.val
  have r := gap_row p
  have lo := (asc_iff r.2.1 (i:=0) (k:=i.val+1) (by omega) (by omega)).mpr (by omega)
  have up := (asc_iff r.2.1 (i:=i.val+1) (k:=h+1) (by omega) (by omega)).mpr (by omega)
  unfold downPosition
  change 3≤smallV (readRank p.val.val) (i.val+1) ∧
    smallV (readRank p.val.val) (i.val+1)<2*h+3
  omega

def coreUp (i : Fin h) : Fin (2*h) :=
  ⟨readRank p.val.val (upPosition i)-3,by have t := upRange hh p i; omega⟩

def coreDown (i : Fin h) : Fin (2*h) :=
  ⟨readRank p.val.val (downPosition i)-3,by have t := downRange hh p i; omega⟩

lemma coreUp_strict : StrictMono (coreUp hh p) := by
  intro i j hij
  have ii := i.isLt
  have jj := j.isLt
  have le : i.val<j.val := hij
  have a := upRange hh p i
  have b := upRange hh p j
  have l := (asc_iff (gap_row p).1 (i:=i.val+2) (k:=j.val+2) (by omega) (by omega)).mpr (by omega)
  change readRank p.val.val (upPosition i) - 3 < readRank p.val.val (upPosition j) - 3
  change readRank p.val.val (upPosition i) < readRank p.val.val (upPosition j) at l
  omega

lemma coreDown_strict : StrictMono (coreDown hh p) := by
  intro i j hij
  have ii := i.isLt
  have jj := j.isLt
  have le : i.val<j.val := hij
  have a := downRange hh p i
  have b := downRange hh p j
  have l := (asc_iff (gap_row p).2.1 (i:=i.val+1) (k:=j.val+1) (by omega) (by omega)).mpr (by omega)
  change readRank p.val.val (downPosition i) - 3 < readRank p.val.val (downPosition j) - 3
  change readRank p.val.val (downPosition i) < readRank p.val.val (downPosition j) at l
  omega

lemma coreCross (i : Fin h) : coreUp hh p i < coreDown hh p i := by
  have hi := i.isLt
  have a := upRange hh p i
  have b := downRange hh p i
  have l := (gap_row p).2.2 (i.val+1) (by omega)
  change readRank p.val.val (upPosition i) - 3 < readRank p.val.val (downPosition i) - 3
  change readRank p.val.val (upPosition i) < readRank p.val.val (downPosition i) at l
  omega

lemma coreDisjoint (i j : Fin h) : coreUp hh p i ≠ coreDown hh p j := by
  have N := smallSize (j:=h+1) (by omega)
  have ii := i.isLt
  have jj := j.isLt
  have a := upRange hh p i
  have b := downRange hh p j
  have hab : upPosition i ≠ downPosition j := by unfold upPosition downPosition uPos vPos; omega
  intro eq
  have eq' := congrArg Fin.val eq
  change readRank p.val.val (upPosition i) - 3 = readRank p.val.val (downPosition j) - 3 at eq'
  exact hab (readRank_inj p.val.val (by unfold upPosition uPos; omega)
    (by unfold downPosition vPos; omega) (by omega))

#print axioms coreDisjoint
end CoverCutoff
