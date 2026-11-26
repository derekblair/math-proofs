import RibbonOddJetSortData
namespace RibbonOddFinite
set_option maxHeartbeats 0
set_option maxRecDepth 30000
theorem verifyJetBank16 : ∀ d : Dir 16, jetBankOk 16 d := by decide +kernel
theorem verifyJetSort16 : ∀ d : Dir 16, sortedOk 16 d := by decide +kernel
theorem verifyJetBank17 : ∀ d : Dir 17, jetBankOk 17 d := by decide +kernel
theorem verifyJetSort17 : ∀ d : Dir 17, sortedOk 17 d := by decide +kernel
theorem verifyJetBank18 : ∀ d : Dir 18, jetBankOk 18 d := by decide +kernel
theorem verifyJetSort18 : ∀ d : Dir 18, sortedOk 18 d := by decide +kernel
theorem verifyJetBank19 : ∀ d : Dir 19, jetBankOk 19 d := by decide +kernel
theorem verifyJetSort19 : ∀ d : Dir 19, sortedOk 19 d := by decide +kernel
end RibbonOddFinite
