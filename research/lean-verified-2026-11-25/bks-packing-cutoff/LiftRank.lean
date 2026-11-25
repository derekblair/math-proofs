import LiftValid
import Mathlib.Data.Prod.Lex

namespace CoverCutoff

def lexKey {h j : ℕ} (p : Equiv.Perm (Fin (SmallN j))) (flip : Bool)
    (v : Fin (BigN h j)) : ℕ ×ₗ ℕ :=
  toLex (bigKey (h:=h) p flip v.val,v.val)

lemma lexKey_inj {h j : ℕ} (p : Equiv.Perm (Fin (SmallN j))) (flip : Bool) :
    Function.Injective (lexKey (h:=h) p flip) :=
  fun _ _ h => Fin.ext (congrArg (fun x => (ofLex x).2) h)

noncomputable def liftRanks {h j : ℕ} (p : Equiv.Perm (Fin (SmallN j))) (flip : Bool) :
    Equiv.Perm (Fin (BigN h j)) :=
  rankKey (lexKey p flip) (lexKey_inj p flip)

lemma lift_less {h j : ℕ} (p : Equiv.Perm (Fin (SmallN j))) (flip : Bool)
    {a b : ℕ} (ha : a<BigN h j) (hb : b<BigN h j)
    (hab : bigKey (h:=h) p flip a<bigKey (h:=h) p flip b) :
    readRank (liftRanks (h:=h) p flip) a<readRank (liftRanks (h:=h) p flip) b := by
  rw [show readRank (liftRanks (h:=h) p flip) a=(liftRanks (h:=h) p flip ⟨a,ha⟩).val from readRank_fin _ ⟨a,ha⟩,
      show readRank (liftRanks (h:=h) p flip) b=(liftRanks (h:=h) p flip ⟨b,hb⟩).val from readRank_fin _ ⟨b,hb⟩]
  exact (rankKey_iff _ _ _ _).mpr (Prod.Lex.lt_iff.mpr (Or.inl hab))

lemma global_transport {h j : ℕ} {f g : ℕ→ℕ} (hh : 2≤h) (hj : 1≤j)
    (hm : ∀ a b, a < BigN h j → b < BigN h j → f a < f b → g a < g b)
    (hG : GlobalRows f h j) : GlobalRows g h j := by
  have hs : BigN h j=3*(h+j)-2 := bigSize hj
  apply (altRows_iff_global hh hj).mp
  obtain ⟨hA,hC,hB,h0,hT⟩ := (altRows_iff_global hh hj).mpr hG
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i hi hi'
    exact hm _ _ (by unfold posA; omega) (by unfold posA; omega) (hA i hi hi')
  · intro i hi hi'
    exact hm _ _ (by unfold posC; omega) (by unfold posC; omega) (hC i hi hi')
  · intro i hi hi'
    exact hm _ _ (by unfold posB; omega) (by unfold posB; omega) (hB i hi hi')
  · exact hm _ _ (by unfold posB; omega) (by unfold posA; omega) h0
  · intro t ht
    obtain ⟨h1,h2,h3⟩ := hT t ht
    exact ⟨hm _ _ (by unfold posA; omega) (by unfold posB; omega) h1,
           hm _ _ (by unfold posB; omega) (by unfold posA; omega) h2,
           hm _ _ (by unfold posA; omega) (by unfold posC; omega) h3⟩

lemma lift_packs {h j : ℕ} (hh : 2≤h) (hj : 1≤j)
    (p : Equiv.Perm (Fin (SmallN j))) (hp : Packs patternA 2 j p) (flip : Bool) :
    Packs (delayed h hh) 3 j (liftRanks p flip) := by
  apply (packs_iff_global hh hj _).mpr
  exact global_transport hh hj (fun a b ha hb => lift_less p flip ha hb)
    (bigKey_global hh hj p ((small_packs_iff p).mp hp) flip)

#print axioms lift_packs
end CoverCutoff
