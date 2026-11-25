import FiberOrder
namespace CoverCutoff

def FiberGap {j : ℕ} (p : Equiv.Perm (Fin (SmallN j))) : Prop :=
  smallV (readRank p) 0 < smallU (readRank p) 2

def FiberBefore {h j : ℕ} (p : Equiv.Perm (Fin (BigN h j))) : Prop :=
  localB (readRank p) (2*h-1) < localC (readRank p) 0

lemma fiberBefore_of_no_gap {h : ℕ} (hh : 2≤h)
    (p : Equiv.Perm (Fin (BigN h (h+1)))) (P : Packs (delayed h hh) 3 (h+1) p)
    (H : ¬ FiberGap (restrictSmall h (h+1) hh (by omega) p)) :
    FiberBefore p := by
  have ns := smallSize (j:=h+1) (by omega)
  have nb := bigSize (h:=h) (j:=h+1) (by omega)
  have cmp := restrict_comparison (j:=h+1) hh (by omega) p
      (a:=vPos 0) (b:=uPos 2) (by unfold vPos; omega) (by unfold uPos; omega)
  rw [kept_V,kept_U,show h-1+2=h+1 by omega] at cmp
  unfold FiberGap smallV smallU at H
  have hAC : localA (readRank p) (h+1) ≤ localC (readRank p) 0 :=
    Nat.le_of_not_gt fun nh => H (cmp.mpr nh)
  have G := (packs_iff_global hh (by omega) p).mp P
  exact ((ab_neg hh (j:=h+1) (by omega) G (i:=h+1) (by omega) (by omega)).mpr
    (Or.inr (by omega))).trans_le hAC

lemma fiber_true_before {h : ℕ} (hh : 2≤h)
    (p : Equiv.Perm (Fin (SmallN (h+1)))) (P : Packs patternA 2 (h+1) p) :
    FiberBefore (h:=h) (liftRanks p true) := by
  have nb := bigSize (h:=h) (j:=h+1) (by omega)
  have k := mainCross (h:=h) p ((small_packs_iff p).mp P) (i:=0) (by omega)
  unfold FiberBefore localB localC
  apply lift_less p true (by unfold posB; omega) (by unfold posC; omega)
  rw [bigKey_B,bigKey_C]
  unfold keyB betweenKey keyC
  rw [if_neg (by omega),show 2*h-1-(h-1)=h by omega,if_neg (by omega)]
  rw [if_pos (Nat.zero_le (h+1))]
  simp only [Bool.true_and,beq_self_eq_true,ite_true]
  simp only [Nat.zero_add] at k
  omega

lemma fiber_false_after {h : ℕ} (hh : 2≤h)
    (p : Equiv.Perm (Fin (SmallN (h+1)))) (H : FiberGap p) :
    ¬ FiberBefore (h:=h) (liftRanks p false) := by
  have nb := bigSize (h:=h) (j:=h+1) (by omega)
  have H' : mainV h p 0 + 3 ≤ mainU h p 2 := by
    unfold FiberGap at H
    unfold mainV mainU
    omega
  have hbc : localC (readRank (liftRanks (h:=h) p false)) 0 <
      localB (readRank (liftRanks (h:=h) p false)) (2*h-1) := by
    unfold localB localC
    apply lift_less p false (by unfold posC; omega) (by unfold posB; omega)
    rw [bigKey_B,bigKey_C]
    rw [show keyC h p 0 = mainV h p 0 by simp [keyC]]
    unfold keyB betweenKey
    rw [if_neg (show ¬ 2*h-1<h-1 by omega),show 2*h-1-(h-1)=h by omega]
    rw [if_neg (show ¬ h+1<h-1 by exact Nat.not_lt_of_ge (Nat.le_trans (Nat.sub_le h 1) (Nat.le_succ h)))]
    simp only [Bool.false_and, Bool.false_eq_true, ite_false]
    rw [show h+1-(h-1)=2 by omega]
    omega
  exact not_lt_of_ge hbc.le

#print axioms fiberBefore_of_no_gap
#print axioms fiber_true_before
#print axioms fiber_false_after
end CoverCutoff
