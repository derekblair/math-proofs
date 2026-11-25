import CatalanRows
import OrderKey

namespace CoverCutoff

abbrev SmallN (j : ℕ) := nVerts 4 2 j
abbrev BigN (h j : ℕ) := nVerts (3*h+1) 3 j

lemma smallSize {j : ℕ} (hj : 1≤j) : SmallN j=2*(j+1) := by unfold SmallN nVerts; omega
lemma bigSize {h j : ℕ} (hj : 1≤j) : BigN h j=3*(h+j)-2 := by unfold BigN nVerts; omega

def keptIndex (h i : ℕ) : ℕ :=
  if i%2=0 then posA (h-1+i/2) else posC (i/2)

lemma kept_U (h i : ℕ) : keptIndex h (uPos i)=posA (h-1+i) := by
  unfold keptIndex uPos
  rw [if_pos (by omega),show 2*i/2=i by omega]

lemma kept_V (h i : ℕ) : keptIndex h (vPos i)=posC i := by
  unfold keptIndex vPos
  rw [if_neg (by omega),show (2*i+1)/2=i by omega]

def embedSmall (h j : ℕ) (hh : 2≤h) (hj : 1≤j) (i : Fin (SmallN j)) : Fin (BigN h j) :=
  ⟨keptIndex h i.val,by
    let v := i.val
    have hi : v < SmallN j := i.isLt
    rw [smallSize hj] at hi
    change keptIndex h v < BigN h j
    rw [bigSize hj]
    unfold keptIndex posA posC
    split_ifs <;> omega⟩

lemma embedSmall_inj (h j : ℕ) (hh : 2≤h) (hj : 1≤j) :
    Function.Injective (embedSmall h j hh hj) := by
  intro a b he
  apply Fin.ext
  have heq : keptIndex h a.val=keptIndex h b.val := congrArg Fin.val he
  unfold keptIndex posA posC at heq
  split_ifs at heq <;> omega

noncomputable def restrictSmall (h j : ℕ) (hh : 2≤h) (hj : 1≤j)
    (p : Equiv.Perm (Fin (BigN h j))) : Equiv.Perm (Fin (SmallN j)) :=
  rankKey (fun a => p (embedSmall h j hh hj a)) (p.injective.comp (embedSmall_inj h j hh hj))

lemma restrict_comparison {h j : ℕ} (hh : 2≤h) (hj : 1≤j)
    (p : Equiv.Perm (Fin (BigN h j))) {a b : ℕ} (ha : a<SmallN j) (hb : b<SmallN j) :
    readRank (restrictSmall h j hh hj p) a < readRank (restrictSmall h j hh hj p) b ↔
    readRank p (keptIndex h a) < readRank p (keptIndex h b) := by
  rw [show readRank (restrictSmall h j hh hj p) a =
    ((restrictSmall h j hh hj p) ⟨a,ha⟩).val from readRank_fin _ ⟨a,ha⟩]
  rw [show readRank (restrictSmall h j hh hj p) b =
    ((restrictSmall h j hh hj p) ⟨b,hb⟩).val from readRank_fin _ ⟨b,hb⟩]
  rw [show keptIndex h a = (embedSmall h j hh hj ⟨a,ha⟩).val from rfl,
      show keptIndex h b = (embedSmall h j hh hj ⟨b,hb⟩).val from rfl]
  rw [readRank_fin,readRank_fin]
  exact rankKey_iff _ _ _ _

lemma restrict_packs {h j : ℕ} (hh : 2≤h) (hj : 1≤j)
    (p : Equiv.Perm (Fin (BigN h j))) (hp : Packs (delayed h hh) 3 j p) :
    Packs patternA 2 j (restrictSmall h j hh hj p) := by
  have hG := (packs_iff_global hh hj p).mp hp
  apply (small_packs_iff _).mpr
  refine ⟨?_,?_,?_⟩
  · intro i _ hi
    unfold smallU
    apply (restrict_comparison hh hj _ (by unfold uPos; rw [smallSize hj]; omega)
        (by unfold uPos; rw [smallSize hj]; omega)).mpr
    rw [kept_U,kept_U]
    exact hG.1 (h-1+i) (by omega) (by omega)
  · intro i _ hi
    unfold smallV
    apply (restrict_comparison hh hj _ (by unfold vPos; rw [smallSize hj]; omega)
        (by unfold vPos; rw [smallSize hj]; omega)).mpr
    rw [kept_V,kept_V]
    exact hG.2.2.1 i (by omega) (by omega)
  · intro t ht
    unfold smallU smallV
    apply (restrict_comparison hh hj _ (by unfold uPos; rw [smallSize hj]; omega)
        (by unfold vPos; rw [smallSize hj]; omega)).mpr
    rw [kept_U,kept_V,show h-1+(t+1)=t+h by omega]
    exact (hG.2.2.2 t ht).2.2.2

#print axioms restrict_packs
end CoverCutoff
