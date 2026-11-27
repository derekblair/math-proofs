import RibbonD3WideJetCheck3
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem jetBlock3 (i : Fin 30) : let z := jetLabel (⟨90+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp z.2.1 z.2.2) (z.1.inp z.2.1 z.2.2) := by
  fin_cases i
  · exact jetChecked90
  · exact jetChecked91
  · exact jetChecked92
  · exact jetChecked93
  · exact jetChecked94
  · exact jetChecked95
  · exact jetChecked96
  · exact jetChecked97
  · exact jetChecked98
  · exact jetChecked99
  · exact jetChecked100
  · exact jetChecked101
  · exact jetChecked102
  · exact jetChecked103
  · exact jetChecked104
  · exact jetChecked105
  · exact jetChecked106
  · exact jetChecked107
  · exact jetChecked108
  · exact jetChecked109
  · exact jetChecked110
  · exact jetChecked111
  · exact jetChecked112
  · exact jetChecked113
  · exact jetChecked114
  · exact jetChecked115
  · exact jetChecked116
  · exact jetChecked117
  · exact jetChecked118
  · exact jetChecked119
end RibbonD3WideFinite
