import RibbonOddPairBankCheck0
import RibbonOddPairBankCheck1
import RibbonOddPairBankCheck2
import RibbonOddPairBankCheck3
import RibbonOddPairBankCheck4
import RibbonOddPairBankCheck5
import RibbonOddPairBankCheck6
namespace RibbonOddFinite
open RibbonStationaryWord RibbonOrderThree
theorem bank_verified (i : Fin 28) (k : Count) : bankOk i k := by
  fin_cases i
  · exact verifyBank0 k
  · exact verifyBank1 k
  · exact verifyBank2 k
  · exact verifyBank3 k
  · exact verifyBank4 k
  · exact verifyBank5 k
  · exact verifyBank6 k
  · exact verifyBank7 k
  · exact verifyBank8 k
  · exact verifyBank9 k
  · exact verifyBank10 k
  · exact verifyBank11 k
  · exact verifyBank12 k
  · exact verifyBank13 k
  · exact verifyBank14 k
  · exact verifyBank15 k
  · exact verifyBank16 k
  · exact verifyBank17 k
  · exact verifyBank18 k
  · exact verifyBank19 k
  · exact verifyBank20 k
  · exact verifyBank21 k
  · exact verifyBank22 k
  · exact verifyBank23 k
  · exact verifyBank24 k
  · exact verifyBank25 k
  · exact verifyBank26 k
  · exact verifyBank27 k
theorem fast_verified (i j : Fin 28) (lt : i.val<j.val) : fastOk i j := by
  fin_cases i
  · exact verifyFast0 j lt
  · exact verifyFast1 j lt
  · exact verifyFast2 j lt
  · exact verifyFast3 j lt
  · exact verifyFast4 j lt
  · exact verifyFast5 j lt
  · exact verifyFast6 j lt
  · exact verifyFast7 j lt
  · exact verifyFast8 j lt
  · exact verifyFast9 j lt
  · exact verifyFast10 j lt
  · exact verifyFast11 j lt
  · exact verifyFast12 j lt
  · exact verifyFast13 j lt
  · exact verifyFast14 j lt
  · exact verifyFast15 j lt
  · exact verifyFast16 j lt
  · exact verifyFast17 j lt
  · exact verifyFast18 j lt
  · exact verifyFast19 j lt
  · exact verifyFast20 j lt
  · exact verifyFast21 j lt
  · exact verifyFast22 j lt
  · exact verifyFast23 j lt
  · exact verifyFast24 j lt
  · exact verifyFast25 j lt
  · exact verifyFast26 j lt
  · change 27 < j.val at lt; omega

theorem pairs_checked (i j : Fin 28) (lt : i.val<j.val) : checkPair i j := by
  let k := pickPair i j
  obtain ⟨a,b,h⟩ := fast_verified i j lt
  rw [←bank_verified i k a,←bank_verified j k b] at h
  exact h

end RibbonOddFinite
#print axioms RibbonOddFinite.pairs_checked
