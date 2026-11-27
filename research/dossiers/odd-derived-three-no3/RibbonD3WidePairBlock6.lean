import RibbonD3WidePairCheck6
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock6 (i : Fin 30) : let z := pairLabel (⟨180+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact pairChecked180
  · exact pairChecked181
  · exact pairChecked182
  · exact pairChecked183
  · exact pairChecked184
  · exact pairChecked185
  · exact pairChecked186
  · exact pairChecked187
  · exact pairChecked188
  · exact pairChecked189
  · exact pairChecked190
  · exact pairChecked191
  · exact pairChecked192
  · exact pairChecked193
  · exact pairChecked194
  · exact pairChecked195
  · exact pairChecked196
  · exact pairChecked197
  · exact pairChecked198
  · exact pairChecked199
  · exact pairChecked200
  · exact pairChecked201
  · exact pairChecked202
  · exact pairChecked203
  · exact pairChecked204
  · exact pairChecked205
  · exact pairChecked206
  · exact pairChecked207
  · exact pairChecked208
  · exact pairChecked209
end RibbonD3WideFinite
