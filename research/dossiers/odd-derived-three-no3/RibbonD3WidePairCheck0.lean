import RibbonD3WidePairData0
import RibbonD3WideOrbitData
import RibbonD3WideRowCheck0
import RibbonD3WideRowCheck1
import RibbonD3WideRowCheck2
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairChecked0 : ∃ w : Cert, good w ((pairLabels[0]!).1.inp 0 0) ((pairLabels[0]!).2.inp 0 0) := by
  exact ⟨pairCerts0[0]!, from_stored rowCheck0 rowCheck2 (by decide +kernel)⟩
theorem pairChecked1 : ∃ w : Cert, good w ((pairLabels[1]!).1.inp 0 0) ((pairLabels[1]!).2.inp 0 0) := by
  exact ⟨pairCerts0[1]!, from_stored rowCheck0 rowCheck3 (by decide +kernel)⟩
theorem pairChecked2 : ∃ w : Cert, good w ((pairLabels[2]!).1.inp 0 0) ((pairLabels[2]!).2.inp 0 0) := by
  exact ⟨pairCerts0[2]!, from_stored rowCheck0 rowCheck4 (by decide +kernel)⟩
theorem pairChecked3 : ∃ w : Cert, good w ((pairLabels[3]!).1.inp 0 0) ((pairLabels[3]!).2.inp 0 0) := by
  exact ⟨pairCerts0[3]!, from_stored rowCheck0 rowCheck6 (by decide +kernel)⟩
theorem pairChecked4 : ∃ w : Cert, good w ((pairLabels[4]!).1.inp 0 0) ((pairLabels[4]!).2.inp 0 0) := by
  exact ⟨pairCerts0[4]!, from_stored rowCheck0 rowCheck8 (by decide +kernel)⟩
theorem pairChecked5 : ∃ w : Cert, good w ((pairLabels[5]!).1.inp 0 0) ((pairLabels[5]!).2.inp 0 0) := by
  exact ⟨pairCerts0[5]!, from_stored rowCheck1 rowCheck13 (by decide +kernel)⟩
theorem pairChecked6 : ∃ w : Cert, good w ((pairLabels[6]!).1.inp 0 0) ((pairLabels[6]!).2.inp 0 0) := by
  exact ⟨pairCerts0[6]!, from_stored rowCheck0 rowCheck14 (by decide +kernel)⟩
theorem pairChecked7 : ∃ w : Cert, good w ((pairLabels[7]!).1.inp 0 0) ((pairLabels[7]!).2.inp 0 0) := by
  exact ⟨pairCerts0[7]!, from_stored rowCheck1 rowCheck18 (by decide +kernel)⟩
theorem pairChecked8 : ∃ w : Cert, good w ((pairLabels[8]!).1.inp 0 0) ((pairLabels[8]!).2.inp 0 0) := by
  exact ⟨pairCerts0[8]!, from_stored rowCheck0 rowCheck19 (by decide +kernel)⟩
theorem pairChecked9 : ∃ w : Cert, good w ((pairLabels[9]!).1.inp 0 0) ((pairLabels[9]!).2.inp 0 0) := by
  exact ⟨pairCerts0[9]!, from_stored rowCheck0 rowCheck20 (by decide +kernel)⟩
theorem pairChecked10 : ∃ w : Cert, good w ((pairLabels[10]!).1.inp 0 0) ((pairLabels[10]!).2.inp 0 0) := by
  exact ⟨pairCerts0[10]!, from_stored rowCheck0 rowCheck22 (by decide +kernel)⟩
theorem pairChecked11 : ∃ w : Cert, good w ((pairLabels[11]!).1.inp 0 0) ((pairLabels[11]!).2.inp 0 0) := by
  exact ⟨pairCerts0[11]!, from_stored rowCheck0 rowCheck23 (by decide +kernel)⟩
theorem pairChecked12 : ∃ w : Cert, good w ((pairLabels[12]!).1.inp 0 0) ((pairLabels[12]!).2.inp 0 0) := by
  exact ⟨pairCerts0[12]!, from_stored rowCheck0 rowCheck25 (by decide +kernel)⟩
theorem pairChecked13 : ∃ w : Cert, good w ((pairLabels[13]!).1.inp 0 0) ((pairLabels[13]!).2.inp 0 0) := by
  exact ⟨pairCerts0[13]!, from_stored rowCheck0 rowCheck30 (by decide +kernel)⟩
theorem pairChecked14 : ∃ w : Cert, good w ((pairLabels[14]!).1.inp 0 0) ((pairLabels[14]!).2.inp 0 0) := by
  exact ⟨pairCerts0[14]!, from_stored rowCheck1 rowCheck31 (by decide +kernel)⟩
theorem pairChecked15 : ∃ w : Cert, good w ((pairLabels[15]!).1.inp 0 0) ((pairLabels[15]!).2.inp 0 0) := by
  exact ⟨pairCerts0[15]!, from_stored rowCheck0 rowCheck32 (by decide +kernel)⟩
theorem pairChecked16 : ∃ w : Cert, good w ((pairLabels[16]!).1.inp 0 0) ((pairLabels[16]!).2.inp 0 0) := by
  exact ⟨pairCerts0[16]!, from_stored rowCheck0 rowCheck33 (by decide +kernel)⟩
theorem pairChecked17 : ∃ w : Cert, good w ((pairLabels[17]!).1.inp 0 0) ((pairLabels[17]!).2.inp 0 0) := by
  exact ⟨pairCerts0[17]!, from_stored rowCheck0 rowCheck35 (by decide +kernel)⟩
theorem pairChecked18 : ∃ w : Cert, good w ((pairLabels[18]!).1.inp 0 0) ((pairLabels[18]!).2.inp 0 0) := by
  exact ⟨pairCerts0[18]!, from_stored rowCheck0 rowCheck37 (by decide +kernel)⟩
theorem pairChecked19 : ∃ w : Cert, good w ((pairLabels[19]!).1.inp 0 0) ((pairLabels[19]!).2.inp 0 0) := by
  exact ⟨pairCerts0[19]!, from_stored rowCheck0 rowCheck40 (by decide +kernel)⟩
theorem pairChecked20 : ∃ w : Cert, good w ((pairLabels[20]!).1.inp 0 0) ((pairLabels[20]!).2.inp 0 0) := by
  exact ⟨pairCerts0[20]!, from_stored rowCheck1 rowCheck43 (by decide +kernel)⟩
theorem pairChecked21 : ∃ w : Cert, good w ((pairLabels[21]!).1.inp 0 0) ((pairLabels[21]!).2.inp 0 0) := by
  exact ⟨pairCerts0[21]!, from_stored rowCheck0 rowCheck44 (by decide +kernel)⟩
theorem pairChecked22 : ∃ w : Cert, good w ((pairLabels[22]!).1.inp 0 0) ((pairLabels[22]!).2.inp 0 0) := by
  exact ⟨pairCerts0[22]!, from_stored rowCheck0 rowCheck46 (by decide +kernel)⟩
theorem pairChecked23 : ∃ w : Cert, good w ((pairLabels[23]!).1.inp 0 0) ((pairLabels[23]!).2.inp 0 0) := by
  exact ⟨pairCerts0[23]!, from_stored rowCheck0 rowCheck51 (by decide +kernel)⟩
theorem pairChecked24 : ∃ w : Cert, good w ((pairLabels[24]!).1.inp 0 0) ((pairLabels[24]!).2.inp 0 0) := by
  exact ⟨pairCerts0[24]!, from_stored rowCheck0 rowCheck53 (by decide +kernel)⟩
theorem pairChecked25 : ∃ w : Cert, good w ((pairLabels[25]!).1.inp 0 0) ((pairLabels[25]!).2.inp 0 0) := by
  exact ⟨pairCerts0[25]!, from_stored rowCheck0 rowCheck54 (by decide +kernel)⟩
theorem pairChecked26 : ∃ w : Cert, good w ((pairLabels[26]!).1.inp 0 0) ((pairLabels[26]!).2.inp 0 0) := by
  exact ⟨pairCerts0[26]!, from_stored rowCheck0 rowCheck57 (by decide +kernel)⟩
theorem pairChecked27 : ∃ w : Cert, good w ((pairLabels[27]!).1.inp 0 0) ((pairLabels[27]!).2.inp 0 0) := by
  exact ⟨pairCerts0[27]!, from_stored rowCheck0 rowCheck59 (by decide +kernel)⟩
theorem pairChecked28 : ∃ w : Cert, good w ((pairLabels[28]!).1.inp 0 0) ((pairLabels[28]!).2.inp 0 0) := by
  exact ⟨pairCerts0[28]!, from_stored rowCheck0 rowCheck60 (by decide +kernel)⟩
theorem pairChecked29 : ∃ w : Cert, good w ((pairLabels[29]!).1.inp 0 0) ((pairLabels[29]!).2.inp 0 0) := by
  exact ⟨pairCerts0[29]!, from_stored rowCheck0 rowCheck62 (by decide +kernel)⟩
end RibbonD3WideFinite
