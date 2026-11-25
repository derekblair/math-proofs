import GapCore
namespace CoverCutoff
open Finset FussCover

variable {h : ℕ} (hh : 2≤h) (p : GapPack h)

def gapUp : Finset (Fin (2*h)) := univ.image (coreUp hh p)
def gapDown : Finset (Fin (2*h)) := univ.image (coreDown hh p)

lemma gapUp_card : (gapUp hh p).card=h := by
  unfold gapUp
  rw [card_image_of_injective _ (coreUp_strict hh p).injective]
  exact Fintype.card_fin h

lemma gapDown_card : (gapDown hh p).card=h := by
  unfold gapDown
  rw [card_image_of_injective _ (coreDown_strict hh p).injective]
  exact Fintype.card_fin h

lemma gapDown_compl : gapDown hh p = (gapUp hh p)ᶜ := by
  apply eq_of_subset_of_card_le
  · intro x
    simp only [gapUp,gapDown,mem_image,mem_univ,true_and,mem_compl]
    intro ⟨d,hd⟩ ⟨u,hu⟩
    exact coreDisjoint hh p u d (hu.trans hd.symm)
  · rw [comp_card _ (gapUp_card hh p),gapDown_card]

lemma gapUp_order :
    (fun i => (gapUp hh p).orderEmbOfFin (gapUp_card hh p) i) = coreUp hh p := by
  apply StrictMono.eq_of_range_eq (Finset.orderEmbOfFin _ _).strictMono (coreUp_strict hh p)
  rw [range_orderEmbOfFin]
  ext x
  simp [gapUp,Set.mem_range]

lemma gapDown_order :
    (fun i => ((gapUp hh p)ᶜ : Finset _).orderEmbOfFin
      (comp_card _ (gapUp_card hh p)) i) = coreDown hh p := by
  apply StrictMono.eq_of_range_eq (Finset.orderEmbOfFin _ _).strictMono (coreDown_strict hh p)
  rw [range_orderEmbOfFin,←gapDown_compl hh p]
  ext x
  simp [gapDown,Set.mem_range]

def gapToBallot : BallotSet h :=
  ⟨gapUp hh p, gapUp_card hh p, by
    apply (ballot_iff_orders _ (gapUp_card hh p)).2
    intro i
    rw [congrFun (gapUp_order hh p) i,congrFun (gapDown_order hh p) i]
    exact coreCross hh p i⟩

#print axioms gapToBallot
end CoverCutoff
