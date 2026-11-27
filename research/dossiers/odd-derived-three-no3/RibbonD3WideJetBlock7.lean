import RibbonD3WideJetCheck7
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem jetBlock7 (i : Fin 30) : let z := jetLabel (⟨210+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp z.2.1 z.2.2) (z.1.inp z.2.1 z.2.2) := by
  fin_cases i
  · exact jetChecked210
  · exact jetChecked211
  · exact jetChecked212
  · exact jetChecked213
  · exact jetChecked214
  · exact jetChecked215
  · exact jetChecked216
  · exact jetChecked217
  · exact jetChecked218
  · exact jetChecked219
  · exact jetChecked220
  · exact jetChecked221
  · exact jetChecked222
  · exact jetChecked223
  · exact jetChecked224
  · exact jetChecked225
  · exact jetChecked226
  · exact jetChecked227
  · exact jetChecked228
  · exact jetChecked229
  · exact jetChecked230
  · exact jetChecked231
  · exact jetChecked232
  · exact jetChecked233
  · exact jetChecked234
  · exact jetChecked235
  · exact jetChecked236
  · exact jetChecked237
  · exact jetChecked238
  · exact jetChecked239
end RibbonD3WideFinite
