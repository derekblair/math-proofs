import PeerRestrict

namespace CoverCutoff

def peerOff (h j : ℕ) : ℕ := (h+j-1)+(h-2)

def peerKey {j : ℕ} (h : ℕ) (p : Equiv.Perm (Fin (SmallN j))) (k : ℕ) : ℕ :=
  let i := k/3
  match k%3 with
  | 0 => if i≤j then peerOff h j + smallV (readRank p) i
         else peerOff h j + SmallN j + (i-(j+1))
  | 1 => h+j-2-i
  | _ => if i<h-2 then h+j-1+i
         else peerOff h j + smallU (readRank p) (i-(h-2))

lemma peerKey_A {h j : ℕ} (p : Equiv.Perm (Fin (SmallN j))) (i : ℕ) :
    localA (peerKey h p) i =
      if i≤j then peerOff h j + smallV (readRank p) i
      else peerOff h j + SmallN j + (i-(j+1)) := by
  unfold localA
  have u : posA i%3=0 := by simp [posA]
  have v : posA i/3=i := by unfold posA;omega
  simp [peerKey,u,v]
lemma peerKey_B {h j : ℕ} (p : Equiv.Perm (Fin (SmallN j))) (i : ℕ) :
    localB (peerKey h p) i = h+j-2-i := by
  unfold localB
  have u : posB i%3=1 := by unfold posB;omega
  have v : posB i/3=i := by unfold posB;omega
  simp [peerKey,u,v]
lemma peerKey_C {h j : ℕ} (p : Equiv.Perm (Fin (SmallN j))) (i : ℕ) :
    localC (peerKey h p) i =
      if i<h-2 then h+j-1+i else peerOff h j + smallU (readRank p) (i-(h-2)) := by
  unfold localC
  have u : posC i%3=2 := by unfold posC;omega
  have v : posC i/3=i := by unfold posC;omega
  simp [peerKey,u,v]

lemma peerKey_valid {h j : ℕ} (hh : 2≤h) (hj : 1≤j) (p : Equiv.Perm (Fin (SmallN j)))
    (P : CatalanRows (readRank p) j) : PeerGlobal (peerKey h p) h j := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i _ bound
    rw [peerKey_B,peerKey_B]; omega
  · intro i _ bound
    rw [peerKey_C,peerKey_C]
    split_ifs with a b b
    · omega
    · unfold peerOff; omega
    · omega
    · have E : i+1-(h-2)=(i-(h-2))+1 := by omega
      rw [E]
      exact Nat.add_lt_add_left (P.1 (i-(h-2)) (by omega) (by omega)) _
  · intro i _ bound
    rw [peerKey_A,peerKey_A]
    split_ifs with a b b
    · exact Nat.add_lt_add_left (P.2.1 i (by omega) (by omega)) _
    · have E : smallV (readRank p) i < SmallN j := readRank_lt p (by
        rw [smallSize hj]; unfold vPos; omega)
      omega
    · omega
    · omega
  · rw [peerKey_B,peerKey_C]
    unfold peerOff; split_ifs <;> omega
  · intro t ht
    rw [peerKey_C,peerKey_A,ite_eq_right (by omega),ite_eq_left (by omega),
        show t+h-1-(h-2)=t+1 by omega]
    exact Nat.add_lt_add_left (P.2.2 t ht) _

def peerLex {h j : ℕ} (p : Equiv.Perm (Fin (SmallN j))) (v : Fin (BigN h j)) : ℕ ×ₗ ℕ :=
  toLex (peerKey h p v.val,v.val)

lemma peerLex_inj {h j : ℕ} (p : Equiv.Perm (Fin (SmallN j))) :
    Function.Injective (peerLex (h:=h) p) :=
  fun _ _ h => Fin.ext (congrArg (fun x => (ofLex x).2) h)

noncomputable def peerLift {h j : ℕ} (p : Equiv.Perm (Fin (SmallN j))) :
    Equiv.Perm (Fin (BigN h j)) := rankKey (peerLex p) (peerLex_inj p)

lemma peerLift_lt {h j : ℕ} (p : Equiv.Perm (Fin (SmallN j))) {a b : ℕ}
    (ha : a<BigN h j) (hb : b<BigN h j) (hab : peerKey h p a<peerKey h p b) :
    readRank (peerLift (h:=h) p) a < readRank (peerLift (h:=h) p) b := by
  rw [show readRank (peerLift (h:=h) p) a = (peerLift (h:=h) p ⟨a,ha⟩).val from readRank_fin _ ⟨a,ha⟩,
      show readRank (peerLift (h:=h) p) b = (peerLift (h:=h) p ⟨b,hb⟩).val from readRank_fin _ ⟨b,hb⟩]
  exact (rankKey_iff _ _ _ _).mpr (Prod.Lex.lt_iff.mpr (Or.inl hab))

lemma peer_lift_valid {h j : ℕ} (hh : 2≤h) (hj : 1≤j) (p : Equiv.Perm (Fin (SmallN j)))
    (P : Packs patternA 2 j p) : Packs (equalWidthPeer h (by omega)) 3 j (peerLift (h:=h) p) := by
  apply (peer_packs_iff hh hj _).mpr
  obtain ⟨B,C,A,H,X⟩ := peerKey_valid hh hj p ((small_packs_iff _).mp P)
  have S := bigSize (h:=h) hj
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i u v
    apply peerLift_lt p (by unfold posB;omega) (by unfold posB;omega)
    exact B i u v
  · intro i u v
    apply peerLift_lt p (by unfold posC;omega) (by unfold posC;omega)
    exact C i u v
  · intro i u v
    apply peerLift_lt p (by unfold posA;omega) (by unfold posA;omega)
    exact A i u v
  · apply peerLift_lt p (by unfold posB;omega) (by unfold posC;omega)
    exact H
  · intro i u
    apply peerLift_lt p (by unfold posC;omega) (by unfold posA;omega)
    exact X i u

end CoverCutoff
