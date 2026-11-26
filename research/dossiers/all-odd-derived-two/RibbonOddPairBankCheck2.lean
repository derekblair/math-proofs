import RibbonOddPairBank
namespace RibbonOddFinite
set_option maxHeartbeats 0
set_option maxRecDepth 30000
theorem verifyBank8 : ∀ k : RibbonStationaryWord.Count, bankOk 8 k := by decide +kernel
theorem verifyFast8 : ∀ j : Fin 28, 8<j.val → fastOk 8 j := by decide +kernel
theorem verifyBank9 : ∀ k : RibbonStationaryWord.Count, bankOk 9 k := by decide +kernel
theorem verifyFast9 : ∀ j : Fin 28, 9<j.val → fastOk 9 j := by decide +kernel
theorem verifyBank10 : ∀ k : RibbonStationaryWord.Count, bankOk 10 k := by decide +kernel
theorem verifyFast10 : ∀ j : Fin 28, 10<j.val → fastOk 10 j := by decide +kernel
theorem verifyBank11 : ∀ k : RibbonStationaryWord.Count, bankOk 11 k := by decide +kernel
theorem verifyFast11 : ∀ j : Fin 28, 11<j.val → fastOk 11 j := by decide +kernel
end RibbonOddFinite
