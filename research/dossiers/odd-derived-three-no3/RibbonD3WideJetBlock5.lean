import RibbonD3WideJetCheck5
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem jetBlock5 (i : Fin 30) : let z := jetLabel (⟨150+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp z.2.1 z.2.2) (z.1.inp z.2.1 z.2.2) := by
  fin_cases i
  · exact jetChecked150
  · exact jetChecked151
  · exact jetChecked152
  · exact jetChecked153
  · exact jetChecked154
  · exact jetChecked155
  · exact jetChecked156
  · exact jetChecked157
  · exact jetChecked158
  · exact jetChecked159
  · exact jetChecked160
  · exact jetChecked161
  · exact jetChecked162
  · exact jetChecked163
  · exact jetChecked164
  · exact jetChecked165
  · exact jetChecked166
  · exact jetChecked167
  · exact jetChecked168
  · exact jetChecked169
  · exact jetChecked170
  · exact jetChecked171
  · exact jetChecked172
  · exact jetChecked173
  · exact jetChecked174
  · exact jetChecked175
  · exact jetChecked176
  · exact jetChecked177
  · exact jetChecked178
  · exact jetChecked179
end RibbonD3WideFinite
