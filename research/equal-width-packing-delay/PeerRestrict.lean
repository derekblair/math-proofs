import PeerWindow

namespace CoverCutoff

def peerIndex (h i : ℕ) : ℕ :=
  if i%2=0 then posC (h-2+i/2) else posA (i/2)

lemma peerIndex_U (h i : ℕ) : peerIndex h (uPos i)=posC (h-2+i) := by
  unfold peerIndex uPos
  rw [ite_eq_left (by omega),show 2*i/2=i by omega]
lemma peerIndex_V (h i : ℕ) : peerIndex h (vPos i)=posA i := by
  unfold peerIndex vPos
  rw [ite_eq_right (by omega),show (2*i+1)/2=i by omega]

def peerEmbed (h j : ℕ) (_hh : 2≤h) (hj : 1≤j) (i : Fin (SmallN j)) : Fin (BigN h j) :=
  ⟨peerIndex h i.val,by
    have E := i.isLt
    change i.val < SmallN j at E
    have X : i.val < 2*(j+1) := by have e := smallSize hj; omega
    rw [bigSize hj]
    unfold peerIndex posA posC
    split_ifs <;> omega⟩

lemma peerEmbed_inj (h j : ℕ) (hh : 2≤h) (hj : 1≤j) :
    Function.Injective (peerEmbed h j hh hj) := by
  intro a b he
  apply Fin.ext
  have eq : peerIndex h a.val=peerIndex h b.val := congrArg Fin.val he
  unfold peerIndex posA posC at eq
  split_ifs at eq <;> omega

noncomputable def peerRestrict (h j : ℕ) (hh : 2≤h) (hj : 1≤j)
    (p : Equiv.Perm (Fin (BigN h j))) : Equiv.Perm (Fin (SmallN j)) :=
  rankKey (fun a => p (peerEmbed h j hh hj a)) (p.injective.comp (peerEmbed_inj h j hh hj))

lemma peer_restrict_cmp {h j : ℕ} (hh : 2≤h) (hj : 1≤j)
    (p : Equiv.Perm (Fin (BigN h j))) {a b : ℕ} (ha : a<SmallN j) (hb : b<SmallN j) :
    readRank (peerRestrict h j hh hj p) a < readRank (peerRestrict h j hh hj p) b ↔
    readRank p (peerIndex h a) < readRank p (peerIndex h b) := by
  let a' : Fin (SmallN j) := ⟨a,ha⟩
  let b' : Fin (SmallN j) := ⟨b,hb⟩
  have u : (peerEmbed h j hh hj a').val=peerIndex h a := rfl
  have v : (peerEmbed h j hh hj b').val=peerIndex h b := rfl
  rw [show a=a'.val by rfl,show b=b'.val by rfl,readRank_fin,readRank_fin,
      ←u,←v,readRank_fin,readRank_fin]
  exact rankKey_iff _ _ _ _

lemma peer_restrict_packs {h j : ℕ} (hh : 2≤h) (hj : 1≤j)
    (p : Equiv.Perm (Fin (BigN h j))) (P : Packs (equalWidthPeer h (by omega)) 3 j p) :
    Packs patternA 2 j (peerRestrict h j hh hj p) := by
  have G := (peer_packs_iff hh hj p).mp P
  apply (small_packs_iff _).mpr
  refine ⟨?_,?_,?_⟩
  · intro i hi hi'
    unfold smallU
    apply (peer_restrict_cmp hh hj p (by rw [smallSize hj];unfold uPos;omega)
      (by rw [smallSize hj];unfold uPos;omega)).mpr
    rw [peerIndex_U,peerIndex_U]
    change localC (readRank p) (h-2+i)<localC (readRank p) (h-2+(i+1))
    exact G.2.1 _ (by omega) (by omega)
  · intro i hi hi'
    unfold smallV
    apply (peer_restrict_cmp hh hj p (by rw [smallSize hj];unfold vPos;omega)
      (by rw [smallSize hj];unfold vPos;omega)).mpr
    rw [peerIndex_V,peerIndex_V]
    exact G.2.2.1 _ (by omega) (by omega)
  · intro i hi
    unfold smallU smallV
    apply (peer_restrict_cmp hh hj p (by rw [smallSize hj];unfold uPos;omega)
      (by rw [smallSize hj];unfold vPos;omega)).mpr
    rw [peerIndex_U,peerIndex_V,show h-2+(i+1)=i+h-1 by omega]
    exact G.2.2.2.2 i hi

end CoverCutoff
