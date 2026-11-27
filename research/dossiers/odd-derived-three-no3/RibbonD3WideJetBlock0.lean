import RibbonD3WideJetCheck0
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem jetBlock0 (i : Fin 30) : let z := jetLabel (⟨0+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp z.2.1 z.2.2) (z.1.inp z.2.1 z.2.2) := by
  fin_cases i
  · exact jetChecked0
  · exact jetChecked1
  · exact jetChecked2
  · exact jetChecked3
  · exact jetChecked4
  · exact jetChecked5
  · exact jetChecked6
  · exact jetChecked7
  · exact jetChecked8
  · exact jetChecked9
  · exact jetChecked10
  · exact jetChecked11
  · exact jetChecked12
  · exact jetChecked13
  · exact jetChecked14
  · exact jetChecked15
  · exact jetChecked16
  · exact jetChecked17
  · exact jetChecked18
  · exact jetChecked19
  · exact jetChecked20
  · exact jetChecked21
  · exact jetChecked22
  · exact jetChecked23
  · exact jetChecked24
  · exact jetChecked25
  · exact jetChecked26
  · exact jetChecked27
  · exact jetChecked28
  · exact jetChecked29
end RibbonD3WideFinite
