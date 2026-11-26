import RibbonOddPairBank
namespace RibbonOddFinite
set_option maxHeartbeats 0
set_option maxRecDepth 30000
theorem verifyBank12 : ∀ k : RibbonStationaryWord.Count, bankOk 12 k := by decide +kernel
theorem verifyFast12 : ∀ j : Fin 28, 12<j.val → fastOk 12 j := by decide +kernel
theorem verifyBank13 : ∀ k : RibbonStationaryWord.Count, bankOk 13 k := by decide +kernel
theorem verifyFast13 : ∀ j : Fin 28, 13<j.val → fastOk 13 j := by decide +kernel
theorem verifyBank14 : ∀ k : RibbonStationaryWord.Count, bankOk 14 k := by decide +kernel
theorem verifyFast14 : ∀ j : Fin 28, 14<j.val → fastOk 14 j := by decide +kernel
theorem verifyBank15 : ∀ k : RibbonStationaryWord.Count, bankOk 15 k := by decide +kernel
theorem verifyFast15 : ∀ j : Fin 28, 15<j.val → fastOk 15 j := by decide +kernel
end RibbonOddFinite
