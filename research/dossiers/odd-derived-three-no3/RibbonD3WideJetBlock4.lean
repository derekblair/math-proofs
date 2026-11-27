import RibbonD3WideJetCheck4
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem jetBlock4 (i : Fin 30) : let z := jetLabel (⟨120+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp z.2.1 z.2.2) (z.1.inp z.2.1 z.2.2) := by
  fin_cases i
  · exact jetChecked120
  · exact jetChecked121
  · exact jetChecked122
  · exact jetChecked123
  · exact jetChecked124
  · exact jetChecked125
  · exact jetChecked126
  · exact jetChecked127
  · exact jetChecked128
  · exact jetChecked129
  · exact jetChecked130
  · exact jetChecked131
  · exact jetChecked132
  · exact jetChecked133
  · exact jetChecked134
  · exact jetChecked135
  · exact jetChecked136
  · exact jetChecked137
  · exact jetChecked138
  · exact jetChecked139
  · exact jetChecked140
  · exact jetChecked141
  · exact jetChecked142
  · exact jetChecked143
  · exact jetChecked144
  · exact jetChecked145
  · exact jetChecked146
  · exact jetChecked147
  · exact jetChecked148
  · exact jetChecked149
end RibbonD3WideFinite
