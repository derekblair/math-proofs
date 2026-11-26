import RibbonOddJetSortData
namespace RibbonOddFinite
set_option maxHeartbeats 0
set_option maxRecDepth 30000
theorem verifyJetBank4 : ∀ d : Dir 4, jetBankOk 4 d := by decide +kernel
theorem verifyJetSort4 : ∀ d : Dir 4, sortedOk 4 d := by decide +kernel
theorem verifyJetBank5 : ∀ d : Dir 5, jetBankOk 5 d := by decide +kernel
theorem verifyJetSort5 : ∀ d : Dir 5, sortedOk 5 d := by decide +kernel
theorem verifyJetBank6 : ∀ d : Dir 6, jetBankOk 6 d := by decide +kernel
theorem verifyJetSort6 : ∀ d : Dir 6, sortedOk 6 d := by decide +kernel
theorem verifyJetBank7 : ∀ d : Dir 7, jetBankOk 7 d := by decide +kernel
theorem verifyJetSort7 : ∀ d : Dir 7, sortedOk 7 d := by decide +kernel
end RibbonOddFinite
