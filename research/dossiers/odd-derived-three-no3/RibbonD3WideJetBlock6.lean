import RibbonD3WideJetCheck6
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem jetBlock6 (i : Fin 30) : let z := jetLabel (⟨180+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp z.2.1 z.2.2) (z.1.inp z.2.1 z.2.2) := by
  fin_cases i
  · exact jetChecked180
  · exact jetChecked181
  · exact jetChecked182
  · exact jetChecked183
  · exact jetChecked184
  · exact jetChecked185
  · exact jetChecked186
  · exact jetChecked187
  · exact jetChecked188
  · exact jetChecked189
  · exact jetChecked190
  · exact jetChecked191
  · exact jetChecked192
  · exact jetChecked193
  · exact jetChecked194
  · exact jetChecked195
  · exact jetChecked196
  · exact jetChecked197
  · exact jetChecked198
  · exact jetChecked199
  · exact jetChecked200
  · exact jetChecked201
  · exact jetChecked202
  · exact jetChecked203
  · exact jetChecked204
  · exact jetChecked205
  · exact jetChecked206
  · exact jetChecked207
  · exact jetChecked208
  · exact jetChecked209
end RibbonD3WideFinite
