import RibbonD3WideJetCheck8
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem jetBlock8 (i : Fin 12) : let z := jetLabel (⟨240+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp z.2.1 z.2.2) (z.1.inp z.2.1 z.2.2) := by
  fin_cases i
  · exact jetChecked240
  · exact jetChecked241
  · exact jetChecked242
  · exact jetChecked243
  · exact jetChecked244
  · exact jetChecked245
  · exact jetChecked246
  · exact jetChecked247
  · exact jetChecked248
  · exact jetChecked249
  · exact jetChecked250
  · exact jetChecked251
end RibbonD3WideFinite
