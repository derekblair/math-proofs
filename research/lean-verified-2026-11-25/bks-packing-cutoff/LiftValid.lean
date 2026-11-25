import LiftKeys

namespace CoverCutoff

lemma keyA_asc {h j : ℕ} (hh : 2≤h) (hj : 1≤j) (p : Equiv.Perm (Fin (SmallN j)))
    (R : CatalanRows (readRank p) j) : Ascending (keyA h p) 0 (h+j) := by
  intro i _ hi
  unfold keyA
  split_ifs with a b <;> try omega
  · have n : i+1-(h-1)=0 := by omega
    rw [n]
    have hB := (mainU_bound (h:=h) p hj (i:=0) (by omega)).1
    unfold liftBase at hB
    omega
  · have hh' : i+1-(h-1)=i-(h-1)+1 := by omega
    rw [hh']
    have hB := mainU_step (h:=h) p R (i:=i-(h-1)) (by omega)
    omega

lemma keyC_asc {h j : ℕ} (hj : 1≤j) (p : Equiv.Perm (Fin (SmallN j)))
    (R : CatalanRows (readRank p) j) : Ascending (keyC h p) 0 (h+j-1) := by
  intro i _ hi
  unfold keyC
  split_ifs with a b <;> try omega
  · have hB := mainV_step (h:=h) p R (i:=i) (by omega)
    omega
  · have hB := (mainV_bound (h:=h) p hj a).2
    omega

lemma between_sandwich {h j : ℕ} (hh : 2≤h) (hj : 1≤j)
    (p : Equiv.Perm (Fin (SmallN j))) (R : CatalanRows (readRank p) j) (flip : Bool)
    {i : ℕ} (hi : i<j) :
    keyA h p i < betweenKey h p flip i ∧ betweenKey h p flip i < keyA h p (i+1) := by
  by_cases ha : i+1<h-1
  · simp only [betweenKey,keyA,if_pos ha,if_pos (show i<h-1 by omega)]
    omega
  have hR : ¬ i+1<h-1 := ha
  by_cases hl : i<h-1
  · have he : i+1-(h-1)=0 := by omega
    have hf : (flip && i==h)=false := by
      have hn : (i==h)=false := by simp [show i≠h by omega]
      simp [hn]
    simp only [betweenKey,keyA,if_neg ha,if_pos hl,hf,Bool.false_eq_true,if_false,he]
    have hB := (mainU_bound (h:=h) p hj (i:=0) (by omega)).1
    unfold liftBase at hB
    omega
  have ea : i+1-(h-1)=i-(h-1)+1 := by omega
  have hstep := mainU_step (h:=h) p R (i:=i-(h-1)) (by omega)
  simp only [betweenKey,keyA,if_neg ha,if_neg hl,ea]
  split_ifs with hf
  · have he : i=h := by simpa using (Bool.and_eq_true_iff.mp hf).2
    have hidx : i-(h-1)=1 := by omega
    rw [hidx] at hstep ⊢
    omega
  · have hB := (mainU_bound (h:=h) p hj (i:=i-(h-1)+1) (by omega)).1
    unfold liftBase at hB
    omega

theorem bigKey_global {h j : ℕ} (hh : 2≤h) (hj : 1≤j)
    (p : Equiv.Perm (Fin (SmallN j))) (R : CatalanRows (readRank p) j) (flip : Bool) :
    GlobalRows (bigKey (h:=h) p flip) h j := by
  apply (altRows_iff_global hh hj).mp
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [Ascending,localA,bigKey_A] using keyA_asc hh hj p R
  · simpa only [Ascending,localC,bigKey_C] using keyC_asc (h:=h) hj p R
  · intro i _ hi
    simp only [localB,bigKey_B,keyB,if_pos (show i<h-1 by omega),if_pos (show i+1<h-1 by omega)]
    omega
  · simp only [localB,localA,bigKey_B,bigKey_A,keyB,keyA,
      if_pos (show h-2<h-1 by omega),if_pos (show 0<h-1 by omega)]
    omega
  · intro t ht
    have hS := between_sandwich hh hj p R flip ht
    have hX := mainCross (h:=h) p R ht
    have hCross : keyA h p (t+h)<keyC h p t := by
      simp only [keyA,keyC,if_neg (show ¬t+h<h-1 by omega),if_pos (show t≤j by omega),
        show t+h-(h-1)=t+1 by omega]
      omega
    simpa only [localA,localB,localC,bigKey_A,bigKey_B,bigKey_C,keyB,
      if_neg (show ¬t+h-1<h-1 by omega),show t+h-1-(h-1)=t by omega] using
      (show keyA h p t<betweenKey h p flip t ∧
        betweenKey h p flip t<keyA h p (t+1) ∧ keyA h p (t+h)<keyC h p t from ⟨hS.1,hS.2,hCross⟩)

#print axioms bigKey_global
end CoverCutoff
