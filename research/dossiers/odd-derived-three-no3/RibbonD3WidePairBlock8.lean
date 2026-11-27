import RibbonD3WidePairCheck8
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock8 (i : Fin 30) : let z := pairLabel (⟨240+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact pairChecked240
  · exact pairChecked241
  · exact pairChecked242
  · exact pairChecked243
  · exact pairChecked244
  · exact pairChecked245
  · exact pairChecked246
  · exact pairChecked247
  · exact pairChecked248
  · exact pairChecked249
  · exact pairChecked250
  · exact pairChecked251
  · exact pairChecked252
  · exact pairChecked253
  · exact pairChecked254
  · exact pairChecked255
  · exact pairChecked256
  · exact pairChecked257
  · exact pairChecked258
  · exact pairChecked259
  · exact pairChecked260
  · exact pairChecked261
  · exact pairChecked262
  · exact pairChecked263
  · exact pairChecked264
  · exact pairChecked265
  · exact pairChecked266
  · exact pairChecked267
  · exact pairChecked268
  · exact pairChecked269
end RibbonD3WideFinite
