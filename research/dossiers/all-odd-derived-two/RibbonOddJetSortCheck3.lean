import RibbonOddJetSortData
namespace RibbonOddFinite
set_option maxHeartbeats 0
set_option maxRecDepth 30000
theorem verifyJetBank12 : ∀ d : Dir 12, jetBankOk 12 d := by decide +kernel
theorem verifyJetSort12 : ∀ d : Dir 12, sortedOk 12 d := by decide +kernel
theorem verifyJetBank13 : ∀ d : Dir 13, jetBankOk 13 d := by decide +kernel
theorem verifyJetSort13 : ∀ d : Dir 13, sortedOk 13 d := by decide +kernel
theorem verifyJetBank14 : ∀ d : Dir 14, jetBankOk 14 d := by decide +kernel
theorem verifyJetSort14 : ∀ d : Dir 14, sortedOk 14 d := by decide +kernel
theorem verifyJetBank15 : ∀ d : Dir 15, jetBankOk 15 d := by decide +kernel
theorem verifyJetSort15 : ∀ d : Dir 15, sortedOk 15 d := by decide +kernel
end RibbonOddFinite
