import PeerLift

namespace CoverCutoff

lemma peer_key_kept {h j : ℕ} (hh : 2≤h) (hj : 1≤j) (p : Equiv.Perm (Fin (SmallN j)))
    (i : Fin (SmallN j)) :
    peerKey h p (peerEmbed h j hh hj i).val = peerOff h j + (p i).val := by
  have E := smallSize hj
  have u := i.isLt
  have h2 : i.val / 2 ≤ j := by omega
  have K : (peerEmbed h j hh hj i).val = peerIndex h i.val := rfl
  rw [K]
  by_cases H : i.val%2=0
  · unfold peerIndex
    rw [ite_eq_left H]
    change localC (peerKey h p) (h-2+i.val/2) = _
    rw [peerKey_C,ite_eq_right (by omega),show h-2+i.val/2-(h-2)=i.val/2 by omega]
    unfold smallU
    rw [show uPos (i.val/2)=i.val by unfold uPos;omega,readRank_fin]
  · unfold peerIndex
    rw [ite_eq_right H]
    change localA (peerKey h p) (i.val/2) = _
    rw [peerKey_A,ite_eq_left h2]
    unfold smallV
    rw [show vPos (i.val/2)=i.val by unfold vPos;omega,readRank_fin]

theorem peer_retract {h j : ℕ} (hh : 2≤h) (hj : 1≤j) (p : Equiv.Perm (Fin (SmallN j))) :
    peerRestrict h j hh hj (peerLift (h:=h) p) = p := by
  apply same_comparisons
  intro a b
  unfold peerRestrict
  rw [rankKey_iff,peerLift,rankKey_iff]
  unfold peerLex
  rw [Prod.Lex.toLex_lt_toLex,peer_key_kept hh hj,peer_key_kept hh hj]
  constructor
  · rintro (H|⟨E,F⟩)
    · change (p a).val < (p b).val
      dsimp only at H
      omega
    · dsimp only at E
      have e : (p a).val=(p b).val := by omega
      have e' : a=b := p.injective (Fin.ext e)
      subst b
      exact (lt_irrefl _ F).elim
  · intro H
    left
    change (p a).val < (p b).val at H
    dsimp only
    omega

inductive PeerLabel (h j : ℕ)
  | reverseB (i : Fin (h+j-1))
  | earlyC (i : Fin (h-2))
  | core (i : Fin (SmallN j))
  | lateA (i : Fin (h-1))

def peerLabelPos {h j : ℕ} (hh : 2≤h) (hj : 1≤j) : PeerLabel h j → Fin (BigN h j)
  | .reverseB i => ⟨posB i.val,by rw [bigSize hj]; unfold posB; have := i.isLt;omega⟩
  | .earlyC i => ⟨posC i.val,by rw [bigSize hj]; unfold posC; have := i.isLt;omega⟩
  | .core i => peerEmbed h j hh hj i
  | .lateA i => ⟨posA (j+1+i.val),by rw [bigSize hj]; unfold posA; have := i.isLt;omega⟩

lemma peerLabel_surj {h j : ℕ} (hh : 2≤h) (hj : 1≤j) :
    Function.Surjective (peerLabelPos hh hj) := by
  intro v
  let i := v.val/3
  have N : v.val < 3*(h+j)-2 := by have e := v.isLt; have H := bigSize (h:=h) hj; omega
  have som : v.val%3=0 ∨ v.val%3=1 ∨ v.val%3=2 := by omega
  rcases som with zero|one|two
  · by_cases lim : i≤j
    · let u : Fin (SmallN j) := ⟨vPos i,by rw [smallSize hj];unfold vPos;omega⟩
      refine ⟨.core u,Fin.ext ?_⟩
      change peerIndex h (vPos i)=v.val
      rw [peerIndex_V]
      unfold posA
      dsimp only [i]
      omega
    · let u : Fin (h-1) := ⟨i-(j+1),by dsimp [i];omega⟩
      refine ⟨.lateA u,Fin.ext ?_⟩
      change posA (j+1+(i-(j+1)))=v.val
      unfold posA
      dsimp only [i] at *
      omega
  · let u : Fin (h+j-1) := ⟨i,by dsimp [i];omega⟩
    refine ⟨.reverseB u,Fin.ext ?_⟩
    change posB i=v.val
    unfold posB
    dsimp only [i]
    omega
  · by_cases lim : i<h-2
    · let u : Fin (h-2) := ⟨i,lim⟩
      refine ⟨.earlyC u,Fin.ext ?_⟩
      change posC i=v.val
      unfold posC
      dsimp only [i]
      omega
    · let u : Fin (SmallN j) := ⟨uPos (i-(h-2)),by rw [smallSize hj];unfold uPos;dsimp [i];omega⟩
      refine ⟨.core u,Fin.ext ?_⟩
      change peerIndex h (uPos (i-(h-2)))=v.val
      rw [peerIndex_U]
      unfold posC
      dsimp only [i] at *
      omega

end CoverCutoff
