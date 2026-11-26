import RibbonOddJetSortData
namespace RibbonOddFinite
set_option maxHeartbeats 0
set_option maxRecDepth 30000
theorem verifyJetBank0 : ∀ d : Dir 0, jetBankOk 0 d := by decide +kernel
theorem verifyJetSort0 : ∀ d : Dir 0, sortedOk 0 d := by decide +kernel
theorem verifyJetBank1 : ∀ d : Dir 1, jetBankOk 1 d := by decide +kernel
theorem verifyJetSort1 : ∀ d : Dir 1, sortedOk 1 d := by decide +kernel
theorem verifyJetBank2 : ∀ d : Dir 2, jetBankOk 2 d := by decide +kernel
theorem verifyJetSort2 : ∀ d : Dir 2, sortedOk 2 d := by decide +kernel
theorem verifyJetBank3 : ∀ d : Dir 3, jetBankOk 3 d := by decide +kernel
theorem verifyJetSort3 : ∀ d : Dir 3, sortedOk 3 d := by decide +kernel
end RibbonOddFinite
