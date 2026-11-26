import RibbonOddPairBank
namespace RibbonOddFinite
set_option maxHeartbeats 0
set_option maxRecDepth 30000
theorem verifyBank16 : ∀ k : RibbonStationaryWord.Count, bankOk 16 k := by decide +kernel
theorem verifyFast16 : ∀ j : Fin 28, 16<j.val → fastOk 16 j := by decide +kernel
theorem verifyBank17 : ∀ k : RibbonStationaryWord.Count, bankOk 17 k := by decide +kernel
theorem verifyFast17 : ∀ j : Fin 28, 17<j.val → fastOk 17 j := by decide +kernel
theorem verifyBank18 : ∀ k : RibbonStationaryWord.Count, bankOk 18 k := by decide +kernel
theorem verifyFast18 : ∀ j : Fin 28, 18<j.val → fastOk 18 j := by decide +kernel
theorem verifyBank19 : ∀ k : RibbonStationaryWord.Count, bankOk 19 k := by decide +kernel
theorem verifyFast19 : ∀ j : Fin 28, 19<j.val → fastOk 19 j := by decide +kernel
end RibbonOddFinite
