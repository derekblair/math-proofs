import RibbonD3WidePairCheck4
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock4 (i : Fin 30) : let z := pairLabel (⟨120+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact pairChecked120
  · exact pairChecked121
  · exact pairChecked122
  · exact pairChecked123
  · exact pairChecked124
  · exact pairChecked125
  · exact pairChecked126
  · exact pairChecked127
  · exact pairChecked128
  · exact pairChecked129
  · exact pairChecked130
  · exact pairChecked131
  · exact pairChecked132
  · exact pairChecked133
  · exact pairChecked134
  · exact pairChecked135
  · exact pairChecked136
  · exact pairChecked137
  · exact pairChecked138
  · exact pairChecked139
  · exact pairChecked140
  · exact pairChecked141
  · exact pairChecked142
  · exact pairChecked143
  · exact pairChecked144
  · exact pairChecked145
  · exact pairChecked146
  · exact pairChecked147
  · exact pairChecked148
  · exact pairChecked149
end RibbonD3WideFinite
