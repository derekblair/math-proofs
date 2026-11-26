import RibbonOddPairBank
namespace RibbonOddFinite
set_option maxHeartbeats 0
set_option maxRecDepth 30000
theorem verifyBank20 : ∀ k : RibbonStationaryWord.Count, bankOk 20 k := by decide +kernel
theorem verifyFast20 : ∀ j : Fin 28, 20<j.val → fastOk 20 j := by decide +kernel
theorem verifyBank21 : ∀ k : RibbonStationaryWord.Count, bankOk 21 k := by decide +kernel
theorem verifyFast21 : ∀ j : Fin 28, 21<j.val → fastOk 21 j := by decide +kernel
theorem verifyBank22 : ∀ k : RibbonStationaryWord.Count, bankOk 22 k := by decide +kernel
theorem verifyFast22 : ∀ j : Fin 28, 22<j.val → fastOk 22 j := by decide +kernel
theorem verifyBank23 : ∀ k : RibbonStationaryWord.Count, bankOk 23 k := by decide +kernel
theorem verifyFast23 : ∀ j : Fin 28, 23<j.val → fastOk 23 j := by decide +kernel
end RibbonOddFinite
