import RibbonOddJetSortCheck0
import RibbonOddJetSortCheck1
import RibbonOddJetSortCheck2
import RibbonOddJetSortCheck3
import RibbonOddJetSortCheck4
import RibbonOddJetSortCheck5
import RibbonOddJetSortCheck6
namespace RibbonOddFinite
open RibbonOrderThree RibbonStationaryWord RibbonOddRowSort
theorem jet_bank_verified (i : Fin 28) (d : Dir i) : jetBankOk i d := by
  fin_cases i
  · exact verifyJetBank0 d
  · exact verifyJetBank1 d
  · exact verifyJetBank2 d
  · exact verifyJetBank3 d
  · exact verifyJetBank4 d
  · exact verifyJetBank5 d
  · exact verifyJetBank6 d
  · exact verifyJetBank7 d
  · exact verifyJetBank8 d
  · exact verifyJetBank9 d
  · exact verifyJetBank10 d
  · exact verifyJetBank11 d
  · exact verifyJetBank12 d
  · exact verifyJetBank13 d
  · exact verifyJetBank14 d
  · exact verifyJetBank15 d
  · exact verifyJetBank16 d
  · exact verifyJetBank17 d
  · exact verifyJetBank18 d
  · exact verifyJetBank19 d
  · exact verifyJetBank20 d
  · exact verifyJetBank21 d
  · exact verifyJetBank22 d
  · exact verifyJetBank23 d
  · exact verifyJetBank24 d
  · exact verifyJetBank25 d
  · exact verifyJetBank26 d
  · exact verifyJetBank27 d
theorem jet_sort_verified (i : Fin 28) (d : Dir i) : sortedOk i d := by
  fin_cases i
  · exact verifyJetSort0 d
  · exact verifyJetSort1 d
  · exact verifyJetSort2 d
  · exact verifyJetSort3 d
  · exact verifyJetSort4 d
  · exact verifyJetSort5 d
  · exact verifyJetSort6 d
  · exact verifyJetSort7 d
  · exact verifyJetSort8 d
  · exact verifyJetSort9 d
  · exact verifyJetSort10 d
  · exact verifyJetSort11 d
  · exact verifyJetSort12 d
  · exact verifyJetSort13 d
  · exact verifyJetSort14 d
  · exact verifyJetSort15 d
  · exact verifyJetSort16 d
  · exact verifyJetSort17 d
  · exact verifyJetSort18 d
  · exact verifyJetSort19 d
  · exact verifyJetSort20 d
  · exact verifyJetSort21 d
  · exact verifyJetSort22 d
  · exact verifyJetSort23 d
  · exact verifyJetSort24 d
  · exact verifyJetSort25 d
  · exact verifyJetSort26 d
  · exact verifyJetSort27 d
theorem jet_sorted_sound (i : Fin 28) (d : Dir i) (p q : Fin 64)
    (lt : p.val<q.val)
    (eq : jetPoint i (direction i d).1 (direction i d).2 (pickJet i d) p =
      jetPoint i (direction i d).1 (direction i d).2 (pickJet i d) q) :
    IsMate (spec (pickJet i d)) p.val q.val := by
  have H := jet_sort_verified i d
  have E := jet_bank_verified i d
  unfold jetBankOk at E
  have same : (storedJet i d)[p.val]! = (storedJet i d)[q.val]! := by
    rw [←E,jet_at,jet_at,congrArg (jetKey i) eq]
  exact checked H p q lt same same

end RibbonOddFinite
#print axioms RibbonOddFinite.jet_sorted_sound
