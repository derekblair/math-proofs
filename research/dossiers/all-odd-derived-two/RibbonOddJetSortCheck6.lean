import RibbonOddJetSortData
namespace RibbonOddFinite
set_option maxHeartbeats 0
set_option maxRecDepth 30000
theorem verifyJetBank24 : ∀ d : Dir 24, jetBankOk 24 d := by decide +kernel
theorem verifyJetSort24 : ∀ d : Dir 24, sortedOk 24 d := by decide +kernel
theorem verifyJetBank25 : ∀ d : Dir 25, jetBankOk 25 d := by decide +kernel
theorem verifyJetSort25 : ∀ d : Dir 25, sortedOk 25 d := by decide +kernel
theorem verifyJetBank26 : ∀ d : Dir 26, jetBankOk 26 d := by decide +kernel
theorem verifyJetSort26 : ∀ d : Dir 26, sortedOk 26 d := by decide +kernel
theorem verifyJetBank27 : ∀ d : Dir 27, jetBankOk 27 d := by decide +kernel
theorem verifyJetSort27 : ∀ d : Dir 27, sortedOk 27 d := by decide +kernel
end RibbonOddFinite
