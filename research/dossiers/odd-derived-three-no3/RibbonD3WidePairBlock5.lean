import RibbonD3WidePairCheck5
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock5 (i : Fin 30) : let z := pairLabel (⟨150+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact pairChecked150
  · exact pairChecked151
  · exact pairChecked152
  · exact pairChecked153
  · exact pairChecked154
  · exact pairChecked155
  · exact pairChecked156
  · exact pairChecked157
  · exact pairChecked158
  · exact pairChecked159
  · exact pairChecked160
  · exact pairChecked161
  · exact pairChecked162
  · exact pairChecked163
  · exact pairChecked164
  · exact pairChecked165
  · exact pairChecked166
  · exact pairChecked167
  · exact pairChecked168
  · exact pairChecked169
  · exact pairChecked170
  · exact pairChecked171
  · exact pairChecked172
  · exact pairChecked173
  · exact pairChecked174
  · exact pairChecked175
  · exact pairChecked176
  · exact pairChecked177
  · exact pairChecked178
  · exact pairChecked179
end RibbonD3WideFinite
