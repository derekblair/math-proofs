import RibbonD3WideJetData0
import RibbonD3WideOrbitData
import RibbonD3JetCheck0
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem jetChecked0 : ∃ w : Cert, good w ((jetLabels[0]!).1.inp (jetLabels[0]!).2.1 (jetLabels[0]!).2.2) ((jetLabels[0]!).1.inp (jetLabels[0]!).2.1 (jetLabels[0]!).2.2) := by
  have e : row ((jetLabels[0]!).1.inp (jetLabels[0]!).2.1 (jetLabels[0]!).2.2) (jetCerts0[0]!).k = (jetCerts0[0]!).A := by decide +kernel
  exact ⟨jetCerts0[0]!, from_stored e e (by decide +kernel)⟩
theorem jetChecked1 : ∃ w : Cert, good w ((jetLabels[1]!).1.inp (jetLabels[1]!).2.1 (jetLabels[1]!).2.2) ((jetLabels[1]!).1.inp (jetLabels[1]!).2.1 (jetLabels[1]!).2.2) := by
  have e : row ((jetLabels[1]!).1.inp (jetLabels[1]!).2.1 (jetLabels[1]!).2.2) (jetCerts0[1]!).k = (jetCerts0[1]!).A := by decide +kernel
  exact ⟨jetCerts0[1]!, from_stored e e (by decide +kernel)⟩
theorem jetChecked2 : ∃ w : Cert, good w ((jetLabels[2]!).1.inp (jetLabels[2]!).2.1 (jetLabels[2]!).2.2) ((jetLabels[2]!).1.inp (jetLabels[2]!).2.1 (jetLabels[2]!).2.2) := by
  have e : row ((jetLabels[2]!).1.inp (jetLabels[2]!).2.1 (jetLabels[2]!).2.2) (jetCerts0[2]!).k = (jetCerts0[2]!).A := by decide +kernel
  exact ⟨jetCerts0[2]!, from_stored e e (by decide +kernel)⟩
theorem jetChecked3 : ∃ w : Cert, good w ((jetLabels[3]!).1.inp (jetLabels[3]!).2.1 (jetLabels[3]!).2.2) ((jetLabels[3]!).1.inp (jetLabels[3]!).2.1 (jetLabels[3]!).2.2) := by
  have e : row ((jetLabels[3]!).1.inp (jetLabels[3]!).2.1 (jetLabels[3]!).2.2) (jetCerts0[3]!).k = (jetCerts0[3]!).A := by decide +kernel
  exact ⟨jetCerts0[3]!, from_stored e e (by decide +kernel)⟩
theorem jetChecked4 : ∃ w : Cert, good w ((jetLabels[4]!).1.inp (jetLabels[4]!).2.1 (jetLabels[4]!).2.2) ((jetLabels[4]!).1.inp (jetLabels[4]!).2.1 (jetLabels[4]!).2.2) := by
  have e : row ((jetLabels[4]!).1.inp (jetLabels[4]!).2.1 (jetLabels[4]!).2.2) (jetCerts0[4]!).k = (jetCerts0[4]!).A := by decide +kernel
  exact ⟨jetCerts0[4]!, from_stored e e (by decide +kernel)⟩
theorem jetChecked5 : ∃ w : Cert, good w ((jetLabels[5]!).1.inp (jetLabels[5]!).2.1 (jetLabels[5]!).2.2) ((jetLabels[5]!).1.inp (jetLabels[5]!).2.1 (jetLabels[5]!).2.2) := by
  have e : row ((jetLabels[5]!).1.inp (jetLabels[5]!).2.1 (jetLabels[5]!).2.2) (jetCerts0[5]!).k = (jetCerts0[5]!).A := by decide +kernel
  exact ⟨jetCerts0[5]!, from_stored e e (by decide +kernel)⟩
theorem jetChecked6 : ∃ w : Cert, good w ((jetLabels[6]!).1.inp (jetLabels[6]!).2.1 (jetLabels[6]!).2.2) ((jetLabels[6]!).1.inp (jetLabels[6]!).2.1 (jetLabels[6]!).2.2) := by
  have e : row ((jetLabels[6]!).1.inp (jetLabels[6]!).2.1 (jetLabels[6]!).2.2) (jetCerts0[6]!).k = (jetCerts0[6]!).A := by decide +kernel
  exact ⟨jetCerts0[6]!, from_stored e e (by decide +kernel)⟩
theorem jetChecked7 : ∃ w : Cert, good w ((jetLabels[7]!).1.inp (jetLabels[7]!).2.1 (jetLabels[7]!).2.2) ((jetLabels[7]!).1.inp (jetLabels[7]!).2.1 (jetLabels[7]!).2.2) := by
  have e : row ((jetLabels[7]!).1.inp (jetLabels[7]!).2.1 (jetLabels[7]!).2.2) (jetCerts0[7]!).k = (jetCerts0[7]!).A := by decide +kernel
  exact ⟨jetCerts0[7]!, from_stored e e (by decide +kernel)⟩
theorem jetChecked8 : ∃ w : Cert, good w ((jetLabels[8]!).1.inp (jetLabels[8]!).2.1 (jetLabels[8]!).2.2) ((jetLabels[8]!).1.inp (jetLabels[8]!).2.1 (jetLabels[8]!).2.2) := by
  have e : row ((jetLabels[8]!).1.inp (jetLabels[8]!).2.1 (jetLabels[8]!).2.2) (jetCerts0[8]!).k = (jetCerts0[8]!).A := by decide +kernel
  exact ⟨jetCerts0[8]!, from_stored e e (by decide +kernel)⟩
theorem jetChecked9 : ∃ w : Cert, good w ((jetLabels[9]!).1.inp (jetLabels[9]!).2.1 (jetLabels[9]!).2.2) ((jetLabels[9]!).1.inp (jetLabels[9]!).2.1 (jetLabels[9]!).2.2) := by
  have e : row ((jetLabels[9]!).1.inp (jetLabels[9]!).2.1 (jetLabels[9]!).2.2) (jetCerts0[9]!).k = (jetCerts0[9]!).A := by decide +kernel
  exact ⟨jetCerts0[9]!, from_stored e e (by decide +kernel)⟩
theorem jetChecked10 : ∃ w : Cert, good w ((jetLabels[10]!).1.inp (jetLabels[10]!).2.1 (jetLabels[10]!).2.2) ((jetLabels[10]!).1.inp (jetLabels[10]!).2.1 (jetLabels[10]!).2.2) := by
  exact ⟨_, RibbonD3Finite.jetChecked0⟩
theorem jetChecked11 : ∃ w : Cert, good w ((jetLabels[11]!).1.inp (jetLabels[11]!).2.1 (jetLabels[11]!).2.2) ((jetLabels[11]!).1.inp (jetLabels[11]!).2.1 (jetLabels[11]!).2.2) := by
  exact ⟨_, RibbonD3Finite.jetChecked1⟩
theorem jetChecked12 : ∃ w : Cert, good w ((jetLabels[12]!).1.inp (jetLabels[12]!).2.1 (jetLabels[12]!).2.2) ((jetLabels[12]!).1.inp (jetLabels[12]!).2.1 (jetLabels[12]!).2.2) := by
  exact ⟨_, RibbonD3Finite.jetChecked2⟩
theorem jetChecked13 : ∃ w : Cert, good w ((jetLabels[13]!).1.inp (jetLabels[13]!).2.1 (jetLabels[13]!).2.2) ((jetLabels[13]!).1.inp (jetLabels[13]!).2.1 (jetLabels[13]!).2.2) := by
  exact ⟨_, RibbonD3Finite.jetChecked3⟩
theorem jetChecked14 : ∃ w : Cert, good w ((jetLabels[14]!).1.inp (jetLabels[14]!).2.1 (jetLabels[14]!).2.2) ((jetLabels[14]!).1.inp (jetLabels[14]!).2.1 (jetLabels[14]!).2.2) := by
  exact ⟨_, RibbonD3Finite.jetChecked4⟩
theorem jetChecked15 : ∃ w : Cert, good w ((jetLabels[15]!).1.inp (jetLabels[15]!).2.1 (jetLabels[15]!).2.2) ((jetLabels[15]!).1.inp (jetLabels[15]!).2.1 (jetLabels[15]!).2.2) := by
  exact ⟨_, RibbonD3Finite.jetChecked5⟩
theorem jetChecked16 : ∃ w : Cert, good w ((jetLabels[16]!).1.inp (jetLabels[16]!).2.1 (jetLabels[16]!).2.2) ((jetLabels[16]!).1.inp (jetLabels[16]!).2.1 (jetLabels[16]!).2.2) := by
  exact ⟨_, RibbonD3Finite.jetChecked6⟩
theorem jetChecked17 : ∃ w : Cert, good w ((jetLabels[17]!).1.inp (jetLabels[17]!).2.1 (jetLabels[17]!).2.2) ((jetLabels[17]!).1.inp (jetLabels[17]!).2.1 (jetLabels[17]!).2.2) := by
  exact ⟨_, RibbonD3Finite.jetChecked7⟩
theorem jetChecked18 : ∃ w : Cert, good w ((jetLabels[18]!).1.inp (jetLabels[18]!).2.1 (jetLabels[18]!).2.2) ((jetLabels[18]!).1.inp (jetLabels[18]!).2.1 (jetLabels[18]!).2.2) := by
  exact ⟨_, RibbonD3Finite.jetChecked8⟩
theorem jetChecked19 : ∃ w : Cert, good w ((jetLabels[19]!).1.inp (jetLabels[19]!).2.1 (jetLabels[19]!).2.2) ((jetLabels[19]!).1.inp (jetLabels[19]!).2.1 (jetLabels[19]!).2.2) := by
  exact ⟨_, RibbonD3Finite.jetChecked9⟩
theorem jetChecked20 : ∃ w : Cert, good w ((jetLabels[20]!).1.inp (jetLabels[20]!).2.1 (jetLabels[20]!).2.2) ((jetLabels[20]!).1.inp (jetLabels[20]!).2.1 (jetLabels[20]!).2.2) := by
  exact ⟨_, RibbonD3Finite.jetChecked10⟩
theorem jetChecked21 : ∃ w : Cert, good w ((jetLabels[21]!).1.inp (jetLabels[21]!).2.1 (jetLabels[21]!).2.2) ((jetLabels[21]!).1.inp (jetLabels[21]!).2.1 (jetLabels[21]!).2.2) := by
  exact ⟨_, RibbonD3Finite.jetChecked11⟩
theorem jetChecked22 : ∃ w : Cert, good w ((jetLabels[22]!).1.inp (jetLabels[22]!).2.1 (jetLabels[22]!).2.2) ((jetLabels[22]!).1.inp (jetLabels[22]!).2.1 (jetLabels[22]!).2.2) := by
  exact ⟨_, RibbonD3Finite.jetChecked12⟩
theorem jetChecked23 : ∃ w : Cert, good w ((jetLabels[23]!).1.inp (jetLabels[23]!).2.1 (jetLabels[23]!).2.2) ((jetLabels[23]!).1.inp (jetLabels[23]!).2.1 (jetLabels[23]!).2.2) := by
  exact ⟨_, RibbonD3Finite.jetChecked13⟩
theorem jetChecked24 : ∃ w : Cert, good w ((jetLabels[24]!).1.inp (jetLabels[24]!).2.1 (jetLabels[24]!).2.2) ((jetLabels[24]!).1.inp (jetLabels[24]!).2.1 (jetLabels[24]!).2.2) := by
  exact ⟨_, RibbonD3Finite.jetChecked14⟩
theorem jetChecked25 : ∃ w : Cert, good w ((jetLabels[25]!).1.inp (jetLabels[25]!).2.1 (jetLabels[25]!).2.2) ((jetLabels[25]!).1.inp (jetLabels[25]!).2.1 (jetLabels[25]!).2.2) := by
  exact ⟨_, RibbonD3Finite.jetChecked15⟩
theorem jetChecked26 : ∃ w : Cert, good w ((jetLabels[26]!).1.inp (jetLabels[26]!).2.1 (jetLabels[26]!).2.2) ((jetLabels[26]!).1.inp (jetLabels[26]!).2.1 (jetLabels[26]!).2.2) := by
  exact ⟨_, RibbonD3Finite.jetChecked16⟩
theorem jetChecked27 : ∃ w : Cert, good w ((jetLabels[27]!).1.inp (jetLabels[27]!).2.1 (jetLabels[27]!).2.2) ((jetLabels[27]!).1.inp (jetLabels[27]!).2.1 (jetLabels[27]!).2.2) := by
  exact ⟨_, RibbonD3Finite.jetChecked17⟩
theorem jetChecked28 : ∃ w : Cert, good w ((jetLabels[28]!).1.inp (jetLabels[28]!).2.1 (jetLabels[28]!).2.2) ((jetLabels[28]!).1.inp (jetLabels[28]!).2.1 (jetLabels[28]!).2.2) := by
  exact ⟨_, RibbonD3Finite.jetChecked18⟩
theorem jetChecked29 : ∃ w : Cert, good w ((jetLabels[29]!).1.inp (jetLabels[29]!).2.1 (jetLabels[29]!).2.2) ((jetLabels[29]!).1.inp (jetLabels[29]!).2.1 (jetLabels[29]!).2.2) := by
  exact ⟨_, RibbonD3Finite.jetChecked19⟩
end RibbonD3WideFinite
