import RibbonOddPairBank
namespace RibbonOddFinite
set_option maxHeartbeats 0
set_option maxRecDepth 30000
theorem verifyBank0 : ∀ k : RibbonStationaryWord.Count, bankOk 0 k := by decide +kernel
theorem verifyFast0 : ∀ j : Fin 28, 0<j.val → fastOk 0 j := by decide +kernel
theorem verifyBank1 : ∀ k : RibbonStationaryWord.Count, bankOk 1 k := by decide +kernel
theorem verifyFast1 : ∀ j : Fin 28, 1<j.val → fastOk 1 j := by decide +kernel
theorem verifyBank2 : ∀ k : RibbonStationaryWord.Count, bankOk 2 k := by decide +kernel
theorem verifyFast2 : ∀ j : Fin 28, 2<j.val → fastOk 2 j := by decide +kernel
theorem verifyBank3 : ∀ k : RibbonStationaryWord.Count, bankOk 3 k := by decide +kernel
theorem verifyFast3 : ∀ j : Fin 28, 3<j.val → fastOk 3 j := by decide +kernel
end RibbonOddFinite
