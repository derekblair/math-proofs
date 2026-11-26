import RibbonOddPairBank
namespace RibbonOddFinite
set_option maxHeartbeats 0
set_option maxRecDepth 30000
theorem verifyBank4 : ∀ k : RibbonStationaryWord.Count, bankOk 4 k := by decide +kernel
theorem verifyFast4 : ∀ j : Fin 28, 4<j.val → fastOk 4 j := by decide +kernel
theorem verifyBank5 : ∀ k : RibbonStationaryWord.Count, bankOk 5 k := by decide +kernel
theorem verifyFast5 : ∀ j : Fin 28, 5<j.val → fastOk 5 j := by decide +kernel
theorem verifyBank6 : ∀ k : RibbonStationaryWord.Count, bankOk 6 k := by decide +kernel
theorem verifyFast6 : ∀ j : Fin 28, 6<j.val → fastOk 6 j := by decide +kernel
theorem verifyBank7 : ∀ k : RibbonStationaryWord.Count, bankOk 7 k := by decide +kernel
theorem verifyFast7 : ∀ j : Fin 28, 7<j.val → fastOk 7 j := by decide +kernel
end RibbonOddFinite
