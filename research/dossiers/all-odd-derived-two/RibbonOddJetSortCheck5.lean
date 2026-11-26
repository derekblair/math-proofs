import RibbonOddJetSortData
namespace RibbonOddFinite
set_option maxHeartbeats 0
set_option maxRecDepth 30000
theorem verifyJetBank20 : ∀ d : Dir 20, jetBankOk 20 d := by decide +kernel
theorem verifyJetSort20 : ∀ d : Dir 20, sortedOk 20 d := by decide +kernel
theorem verifyJetBank21 : ∀ d : Dir 21, jetBankOk 21 d := by decide +kernel
theorem verifyJetSort21 : ∀ d : Dir 21, sortedOk 21 d := by decide +kernel
theorem verifyJetBank22 : ∀ d : Dir 22, jetBankOk 22 d := by decide +kernel
theorem verifyJetSort22 : ∀ d : Dir 22, sortedOk 22 d := by decide +kernel
theorem verifyJetBank23 : ∀ d : Dir 23, jetBankOk 23 d := by decide +kernel
theorem verifyJetSort23 : ∀ d : Dir 23, sortedOk 23 d := by decide +kernel
end RibbonOddFinite
