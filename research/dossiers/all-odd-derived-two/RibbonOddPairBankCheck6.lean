import RibbonOddPairBank
namespace RibbonOddFinite
set_option maxHeartbeats 0
set_option maxRecDepth 30000
theorem verifyBank24 : ∀ k : RibbonStationaryWord.Count, bankOk 24 k := by decide +kernel
theorem verifyFast24 : ∀ j : Fin 28, 24<j.val → fastOk 24 j := by decide +kernel
theorem verifyBank25 : ∀ k : RibbonStationaryWord.Count, bankOk 25 k := by decide +kernel
theorem verifyFast25 : ∀ j : Fin 28, 25<j.val → fastOk 25 j := by decide +kernel
theorem verifyBank26 : ∀ k : RibbonStationaryWord.Count, bankOk 26 k := by decide +kernel
theorem verifyFast26 : ∀ j : Fin 28, 26<j.val → fastOk 26 j := by decide +kernel
theorem verifyBank27 : ∀ k : RibbonStationaryWord.Count, bankOk 27 k := by decide +kernel
end RibbonOddFinite
