import RibbonD3WidePairCheck3
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock3 (i : Fin 30) : let z := pairLabel (⟨90+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact pairChecked90
  · exact pairChecked91
  · exact pairChecked92
  · exact pairChecked93
  · exact pairChecked94
  · exact pairChecked95
  · exact pairChecked96
  · exact pairChecked97
  · exact pairChecked98
  · exact pairChecked99
  · exact pairChecked100
  · exact pairChecked101
  · exact pairChecked102
  · exact pairChecked103
  · exact pairChecked104
  · exact pairChecked105
  · exact pairChecked106
  · exact pairChecked107
  · exact pairChecked108
  · exact pairChecked109
  · exact pairChecked110
  · exact pairChecked111
  · exact pairChecked112
  · exact pairChecked113
  · exact pairChecked114
  · exact pairChecked115
  · exact pairChecked116
  · exact pairChecked117
  · exact pairChecked118
  · exact pairChecked119
end RibbonD3WideFinite
