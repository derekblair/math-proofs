import RibbonOddJetSortData
namespace RibbonOddFinite
set_option maxHeartbeats 0
set_option maxRecDepth 30000
theorem verifyJetBank8 : ∀ d : Dir 8, jetBankOk 8 d := by decide +kernel
theorem verifyJetSort8 : ∀ d : Dir 8, sortedOk 8 d := by decide +kernel
theorem verifyJetBank9 : ∀ d : Dir 9, jetBankOk 9 d := by decide +kernel
theorem verifyJetSort9 : ∀ d : Dir 9, sortedOk 9 d := by decide +kernel
theorem verifyJetBank10 : ∀ d : Dir 10, jetBankOk 10 d := by decide +kernel
theorem verifyJetSort10 : ∀ d : Dir 10, sortedOk 10 d := by decide +kernel
theorem verifyJetBank11 : ∀ d : Dir 11, jetBankOk 11 d := by decide +kernel
theorem verifyJetSort11 : ∀ d : Dir 11, sortedOk 11 d := by decide +kernel
end RibbonOddFinite
