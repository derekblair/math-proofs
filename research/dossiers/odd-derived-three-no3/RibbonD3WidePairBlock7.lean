import RibbonD3WidePairCheck7
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock7 (i : Fin 30) : let z := pairLabel (⟨210+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact pairChecked210
  · exact pairChecked211
  · exact pairChecked212
  · exact pairChecked213
  · exact pairChecked214
  · exact pairChecked215
  · exact pairChecked216
  · exact pairChecked217
  · exact pairChecked218
  · exact pairChecked219
  · exact pairChecked220
  · exact pairChecked221
  · exact pairChecked222
  · exact pairChecked223
  · exact pairChecked224
  · exact pairChecked225
  · exact pairChecked226
  · exact pairChecked227
  · exact pairChecked228
  · exact pairChecked229
  · exact pairChecked230
  · exact pairChecked231
  · exact pairChecked232
  · exact pairChecked233
  · exact pairChecked234
  · exact pairChecked235
  · exact pairChecked236
  · exact pairChecked237
  · exact pairChecked238
  · exact pairChecked239
end RibbonD3WideFinite
